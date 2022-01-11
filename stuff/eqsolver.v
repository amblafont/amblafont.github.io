
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section MonadicEq.

Context (ob : Type).
Declare Scope object_scope.
Delimit Scope object_scope with o.
Bind Scope object_scope with ob.
Context (mor : ob -> ob -> Type).
Declare Scope mor_scope.
Delimit Scope mor_scope with m.
Bind Scope mor_scope with mor.

Context (id : forall a, mor a a).
Arguments id {a}.

Context (comp : forall a b c, mor b c -> mor a b -> mor a c).
Infix "$" := comp (at level 32, right associativity).
Notation "a ;; b" := (b $ a) (at level 31, left associativity, only parsing).

Context (comp_assoc : forall `(a : mor x3 x4)
                        `(b : mor x2 x3)
                        `(c : mor x1 x2),
                        ((a $ b) $ c = a $ b $ c)).
Hint Rewrite comp_assoc : monad.

Context (idl: forall `(b : mor x y), id $ b = b).
Hint Rewrite idl : monad.

Context (idr: forall `(b : mor x y), b $ id = b).
Hint Rewrite idr : monad.

Context (sumo : ob -> ob -> ob).
Infix "+" := sumo : object_scope.

Context (copairm : forall a b c, mor a c -> mor b c -> mor (a + b) c).
Infix "||" := copairm.

Context (i₁ : forall x y, mor x (x + y)).
Arguments i₁ {x} {y}.

Context (i₂ : forall x y, mor y (x + y)).
Arguments i₂ {x} {y}.

Definition summ {a b a' b'} (s1 : mor a b) (s2 : mor a' b') : mor (a + a') (b + b')
  := i₁ $ s1 || i₂ $ s2.
Infix "+" := summ : mor_scope.

Lemma summ_def {a b a' b'} (s1 : mor a b) (s2 : mor a' b') :
  summ s1 s2 = i₁ $ s1 || i₂ $ s2.
  reflexivity.
Qed.

Hint Rewrite @summ_def : monad.

Context (mor_copairm : forall
            `(m : mor c b)
           `(t1 : mor x1 c)
           `(t2 : mor x2 c),
             m $ (t1 || t2) = (m $ t1) || (m $ t2)).
Hint Rewrite mor_copairm : monad.

Context (copairm_i₁ : forall
           `(s1 : mor x1 c)
           `(s2 : mor x2 c),
             (s1 || s2) $ i₁ = s1).
Hint Rewrite copairm_i₁ : monad.

Context (copairm_i₂ : forall
           `(s1 : mor x1 c)
           `(s2 : mor x2 c),
             (s1 || s2) $ i₂ = s2).
Hint Rewrite copairm_i₂ : monad.


Lemma mor_copairm_ctxt : forall
            `(m : mor c b)
           `(t1 : mor x1 c)
           `(t2 : mor x2 c)
           `(x : mor d _) ,
             m $ (t1 || t2) $ x = ((m $ t1) || (m $ t2)) $ x.
Proof.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @mor_copairm_ctxt : monad.

Lemma copairm_i₁_ctxt : forall
           `(x : mor a x1)
           `(s1 : mor x1 c)
           `(s2 : mor x2 c),
             (s1 || s2) $ i₁ $ x = s1 $ x.
Proof.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @copairm_i₁_ctxt : monad.


Lemma copairm_i₂_ctxt : forall
           `(x : mor a x2)
           `(s1 : mor x1 c)
           `(s2 : mor x2 c),
             (s1 || s2) $ i₂ $ x = s2 $ x.
Proof.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @copairm_i₂_ctxt : monad.

Section MonadDef.

Context (S : ob -> ob)
        (bind : forall a b, mor a (S b) -> mor (S a) (S b))
        (η : forall x, mor x (S x)).



(*
Class is_monad : Prop :=
  {
  bind_eta : forall X, [@η X] = id ;
  bind_bind : forall `(s : mor b (S c))
                       `(s' : mor c (S d)),
                       [ s ] ;; [ s' ] = [ s ;; [ s' ]  ];
  η_bind : forall `(s : mor b (S c)) , (η ;; [ s ] = s)
  }.
*)
End MonadDef.

  Record monad :=
    {
    M :> ob -> ob ;
    bind : forall a b, mor a (M b) -> mor (M a) (M b) ;
    η : forall x, mor x (M x) ;
    (* mon_laws : is_monad bind η *)
    bind_eta : forall X, bind (@η X) = id ;
    bind_bind : forall `(s : mor b (M c))
                  `(s' : mor c (M d)),
        bind s ;; bind s'  = bind ( s ;; bind s' )  ;
    η_bind : forall `(s : mor b (M c)) , (η b ;; bind s  = s)
    }.

  Arguments M _ x%object_scope.
Hint Rewrite @bind_eta : monad.
Hint Rewrite @bind_bind : monad.
Hint Rewrite @η_bind : monad.

Notation "[ x ]" := (bind x).
Arguments η {m} {x}.
     
Section MonadLawsCtxt.
  Context (S : monad).

Lemma bind_bind_ctxt : forall `(x : mor a (S b))
                       `(s : mor b (S c))
                       `(s' : mor c (S d)),
                       x ;; [ s ] ;; [ s' ]  = x ;; [ s ;; [ s' ]  ].
Proof.
  intros; rewrite <- comp_assoc. f_equal ; autorewrite with monad; reflexivity.
Qed.

Lemma η_bind_ctxt : forall `(x : mor a b)
                    `(s : mor b (S c)) 
          , (x ;; η ;; [ s ] = x ;; s).
Proof.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
End MonadLawsCtxt.

Hint Rewrite @bind_bind_ctxt : monad.
Hint Rewrite @η_bind_ctxt : monad.


Notation "# S f" := [η (m := S) $ f] (at level 30, S at level 2).

Context (S : monad).
Arguments S _%object_scope : extra scopes.

(* Definition μ { a } : mor (S (S a)) (S a) := [ id ]. *)
Notation μ := [ id ].


Definition γs {X : monad} {a b} : mor (M X (a + X b))
                      (M X (a + b))
                    := [ η $ i₁ || (# X i₂) ].


Definition t1 (G X : ob) : mor (S (S (G + X + S X) + S X + S (S X)))
                               (S (G + X + X)) :=
  γs ;;  (* S (γ + id + id) *)
    # S (γs + id + id) ;;
    (* S [ id, S i2, S i3 ] *)
    # S (id ||  # S (i₁ $ i₂) || # S i₂) ;;
    (* μ *)
    μ.

Definition t2 (G X : ob) : mor (S (S (G + X + S X) + S X + S (S X)))
                               (S (G + X + X)) :=
   (* S(id+μ) *)
      # S (id + μ)
   (* S([id,Sι₂] + id) *)
    ;; # S ((id || # S (i₁ $ i₂)) + id)
    (* S[id,η∘ι₃]*)
    ;; # S (id || η $ i₂ $ id)
    (* μ *)
    ;; μ
    (* γ *)
    ;; γs.

Lemma lemmeG : (forall G X, t1 G X = t2 G X).
  intros.
  unfold t1, t2, summ, γs, μ.
  autorewrite with monad.
  reflexivity.
Qed.
  

Context (G : ob -> ob -> ob)
        (Gₘ : forall `(mor a b) `(mor a' b'), mor (G a a') (G b b') ).

Context (Gcomp : forall
            `(f1 : mor a1 b1) `(g1 : mor a'1 b'1)
            `(f2 : mor b1 c2) `(g2 : mor b'1 c'2),
            Gₘ f2 g2 $ Gₘ f1 g1 = Gₘ (f2 $ f1) (g2 $ g1)
        ).

Hint Rewrite Gcomp : monad.

Lemma Gcomp_ctxt : forall `(x : mor o (G a1 a'1))
            `(f1 : mor a1 b1) `(g1 : mor a'1 b'1)
            `(f2 : mor b1 c2) `(g2 : mor b'1 c'2),
            Gₘ f2 g2 $ Gₘ f1 g1 $ x = Gₘ (f2 $ f1) (g2 $ g1) $ x.
Proof.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @Gcomp_ctxt : monad.

Context (Gid : forall X Y, Gₘ (@id X) (@id Y) = id).
Hint Rewrite Gid: monad.

Section Homogene.
Context (h : forall X Y, mor (G (S X) (S Y)) (S (G (S X) Y + Y + S X))).
Arguments h {X} {Y}.

Context (hax : forall X Y,
            (* ltac:(let x =  *)
            (Gₘ μ id ;; @h X Y = h ;; # S (Gₘ μ id + id + id) ;; # S (id + id + μ))).

(* Corollary hax_simpl X Y : *)
Hint Rewrite hax : monad.

Lemma hax_ctxt : forall X Y `(f : mor a (S Y)),
  @h X Y $ Gₘ μ f = [η $ i₁ $ i₁ $ Gₘ μ id || η $ i₁ $ i₂ || η $ i₂ $ μ] $ h $ Gₘ id f.
  intros; rewrite <- (idl f).
  rewrite <- (idr [id]).
  intros; rewrite <- Gcomp, <- comp_assoc.
  f_equal; rewrite hax. autorewrite with monad.
  reflexivity.
Qed.

Hint Rewrite hax_ctxt : monad.

Context (hμ : forall X Y, Gₘ id μ ;; @h X Y = h ;; # S ((h || # S (i₁ $ i₂)) + id)
         ;;  # S (id || η $ i₂)  ;; μ).

Hint Rewrite hμ : monad.

Lemma hμ_ctxt : forall X Y `(f : mor A _), Gₘ f μ ;; @h X Y =
                                      Gₘ f id ;; h ;; # S ((h || # S (i₁ $ i₂)) + id)
         ;;  # S (id || η $ i₂)  ;; μ.
  intros; rewrite <- (idl f).
  rewrite <- (idr [id]).
  intros; rewrite <- Gcomp, <- comp_assoc.
  f_equal; rewrite hμ. autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite hμ_ctxt : monad.


(* c'etait pas necessaire adns la preuve a la main *)
Context (hnat : forall `(f : mor Z X)`(g : mor W Y), @h X Y $ Gₘ (# S f) (# S g) =
                                               # S (Gₘ (# S f) g + g + # S f) $ h 
        ).
Lemma hnat_helper1 :
  forall `(f : mor Z X) Y, @h X Y $ Gₘ (# S f) id =
                                               # S (Gₘ (# S f) id + id + # S f) $ h .
  intros.
  rewrite <- hnat.
  autorewrite with monad.
  reflexivity.
Qed.

Hint Rewrite @hnat_helper1 : monad.

Definition Sa `(a : mor (G (S X) X) X) : mor (G (S (S X)) (S X)) (S X) :=
  Gₘ μ id ;; h ;; γs ;; # S (a || id || id).

Context (X : ob) (a : mor (G (S X) X) X) .

Definition r :=
    [[η $ a $ Gₘ μ id || η || μ] $ h || id || μ] $ h $ Gₘ (# S μ) id =
  [[η $ a $ Gₘ [μ] id || η || [μ]] $ h || id || [μ]] $ h.

Definition r_sans_ax :=  
  [[η $ a || η || id] $ h || id || id] $ h $ Gₘ [μ] id = [[η $ a || η || id] $ h $ Gₘ μ id || id || μ] $ h $ Gₘ μ id
.



(* Check (eq_refl :r = r_sans_ax). *)

Lemma μ_mor :
  Gₘ (# S μ) μ ;; Sa a = Sa (Sa a) ;; μ.
Proof.
  unfold Sa, γs.
  cbn.
  (* le hmmu est bien utilise, et hax aussi.. *)
  autorewrite with monad.
  reflexivity.
Qed.




End Homogene.
Section RelativeProp62.
  (* based on Proposition 6.2 de Monads as extension systems *)

Context (T : monad).
Arguments T _%object_scope : extra scopes.
(* STY est une T-algebre (au sens de relative monads, def 2.11 de Altenkirch & cie) *)
Context (bind' : forall `(f : mor X (S (T Y))), mor (T X) (S (T Y))).
Notation "⟦ f ⟧" := (bind' f).

Context (bind'_η : forall `(f : mor X (S (T Y))),
             ⟦ f ⟧ $ η = f
        ).
Context (bind'_bind : forall `(k : mor Z (T W))
                         `(f : mor W (S (T X))),
                               ⟦ f ⟧ $ [ k ] = ⟦ ⟦ f ⟧ $ k ⟧
        ).

(* forall h :  b → Ta, [η $ [ h ]] is an T-algebra map*)
Context (bind'_nat : forall `(h : mor b (T a))
                       `(f : mor Z _)
          ,
            [η $ [ h ]] $ ⟦ f ⟧ = ⟦ [η $ [ h ]] $ f ⟧
        ).

Context (bind'_bind' : forall `(s : mor b (S (T c)))
                  `(s' : mor c (S (T d))),
      [⟦ s' ⟧] $ ⟦ s ⟧ = ⟦ [⟦ s' ⟧] $ s ⟧).

Context (bind'_ηη : forall X, ⟦ η $ η (x := X) ⟧ = η).


Hint Rewrite bind'_nat bind'_η bind'_bind bind'_ηη bind'_bind' : monad.

Lemma bind'_η_ctxt : forall `(f : mor X (S (T Y))) `(g : mor Z _),
             ⟦ f ⟧ $ η $ g = f $ g.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Lemma bind'_bind_ctxt : forall `(k : mor Z (T W))
                     `(f : mor W (S (T X)))
                     `(g : mor Z _)
  ,
                               ⟦ f ⟧ $ [ k ] $ g = ⟦ ⟦ f ⟧ $ k ⟧ $ g.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.

Lemma bind'_nat_ctxt : forall `(h : mor b (T a))
                       `(f : mor Z _)
                       `(g : mor W _)
          ,
            [η $ [ h ]] $ ⟦ f ⟧ $ g = ⟦ [η $ [ h ]] $ f ⟧ $ g .
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.

Lemma bind'_bind'_ctxt : forall `(s : mor b (S (T c)))
                  `(s' : mor c (S (T d)))
                     `(g : mor Z _),
      [⟦ s' ⟧] $ ⟦ s ⟧ $ g = ⟦ [⟦ s' ⟧] $ s ⟧ $ g.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.

Hint Rewrite @bind'_η_ctxt @bind'_bind_ctxt @bind'_bind'_ctxt : monad.


Lemma sanity_check `(f : mor X (S (T Y))) : ⟦ f ⟧ = ⟦ id ⟧ $ # T f.
Proof.
  autorewrite with monad.
  reflexivity.
Qed.

Definition STS_ST {X} : mor (S (T (S X))) (S (T X)) :=  [⟦ # S η ⟧].
Hint Rewrite (fun X => eq_refl : @STS_ST X = [⟦ # S η ⟧]) : monad.
Notation μST := [⟦ id ⟧].

Lemma bind_of_bind' `(f : mor X (S (T Y)))  : [ ⟦ f ⟧] = μST $ # S (# T f).
  autorewrite with monad.
  reflexivity.
Qed.

Context (h : forall X Y, mor (G (S (T X)) (S Y)) (S (T (G (S (T X)) Y + Y + S (T X))))).
Arguments h {X} {Y}.
Context (hax : forall X Y ,
            Gₘ μST id ;; @h X Y = h ;;
                                  # S (# T (Gₘ μST id + id + id))
                                  ;; # S ( # T (id + id + μST))).
Hint Rewrite hax : monad.

Lemma hax_ctxt_rel : forall X Y `(f : mor Z _),
    Gₘ [ ⟦ f ⟧ ] id ;; @h X Y =
    Gₘ (# S (# T f)) id ;;
    h ;;
                                  # S (# T (Gₘ μST id + id + id))
                                  ;; # S ( # T (id + id + μST)).
  Proof.
    intros.
    rewrite bind_of_bind'.
  rewrite <- (idr (id (a := S Y))).
  intros; rewrite <- Gcomp, <- comp_assoc.
  f_equal; rewrite hax. autorewrite with monad.
  reflexivity.
  Qed.
  Hint Rewrite hax_ctxt_rel : monad.


(* Lemma hax' X Y `(f : mor a (S Y)) : *)
(*     @h X Y $ Gₘ [# S (η (m := T))] f = Gₘ (# S η) f ;; h  ;; *)
(*                                   # S (# T (Gₘ STS_ST id + id + id)) *)
(*                                   ;; # S (# T (id + id + STS_ST)) . *)
(* Admitted. *)
  (*
Context ( hax' : forall X Y `(f : mor a (S Y)) ,
    @h X Y $ Gₘ [# S (η (m := T))] f = Gₘ (# S η) f ;; h  ;;
                                  # S (# T (Gₘ STS_ST id + id + id))
                                  ;; # S (# T (id + id + STS_ST)) ).
Hint Rewrite hax' : monad.
*)

  (* TODO c'est pas le bon! *)
Context (hμ : forall X Y  , Gₘ id μ ;; @h X Y = h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST).
Hint Rewrite hμ : monad.

Corollary hμ_ctxt1 : forall X Y `(f : mor A _) , Gₘ f μ ;; @h X Y = Gₘ f id ;; h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST.
  intros; rewrite <- (idl f).
  rewrite <- (idr [id]).
  intros; rewrite <- Gcomp, <- comp_assoc.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite hμ_ctxt1 : monad.
  (*
Context (hμ : forall X Y  , Gₘ id μ ;; @h X Y = h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST).
Hint Rewrite hμ : monad.

Corollary hμ_ctxt1 : forall X Y `(f : mor A _) , Gₘ f μ ;; @h X Y = Gₘ f id ;; h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST.
  intros; rewrite <- (idl f).
  rewrite <- (idr [id]).
  intros; rewrite <- Gcomp, <- comp_assoc.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite hμ_ctxt1 : monad.
*)

Context (hnat : forall `(f : mor Z X)`(g : mor W Y), @h X Y $ Gₘ (# S (# T f)) (# S g) =
                                               # S (# T (Gₘ (# S (# T f)) g + g + # S (# T f))) $ h 
        ).
Lemma hnat'_helper1 :
 forall `(f : mor Z X) Y, @h X Y $ Gₘ (# S (# T f)) id =
                                               # S (# T (Gₘ (# S (# T f)) id + id + # S (# T f))) $ h .
  intros.
  rewrite <- hnat.
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite @hnat'_helper1 : monad.

Definition γsST  {a b} : mor (S (T (a + (S (T b)))))
                      (S (T (a + b))) :=
   # S (# T (η $ η $ i₁ || # S (# T i₂)) ) ;; μST .
Definition Sa'
           `(a : mor (G (S (T X)) X) X)
           (b : mor (T X) X)
  : mor (G (S (T (S X))) (S X)) (S X):=
  Gₘ STS_ST id ;; h ;; γsST ;;
  # S (# T (a || id || id)) ;;
        # S b.

Lemma Sa'_simpl 
           `(a : mor (G (S (T X)) X) X)
           (b : mor (T X) X) :
  Sa' a b =
  [# S (b $ [η $ a || η || η]) $ ⟦ η $ η $ i₁ || # S (# T i₂) ⟧] $ h $ Gₘ [⟦ # S η ⟧] id.

  unfold Sa',γsST.
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite @Sa'_simpl : monad.
Definition Sb'
           `(b : mor (T X) X)
  : mor (T (S X)) (S X) :=
   ⟦ # S η ⟧ ;; # S b.

Lemma Sb'_simpl `(b : mor (T X) X) :
  Sb' b = 
   ⟦ # S η ⟧ ;; # S b.
  reflexivity.
Qed.
Hint Rewrite @Sb'_simpl : monad.
Context (X : ob)
        (* (a : mor (G (S X) X) X) *)
        (a : mor (G (S (T X)) X) X).
(* structure de T-algebre en mode relatif *)

Context (bindX : forall `(f : mor Y X), mor (T Y) X).
(* Declare Scope X_scope. *)
(* Delimit Scope X_scope with x. *)
Notation "⦃ x ⦄" := (bindX x).

Context (bindX_η : forall `(f : mor Z X),
             ⦃ f ⦄ $ η = f
        ).
Context (bindX_bind : forall `(k : mor Z (T W))
                         `(f : mor W X),
                               ⦃ f ⦄ $ [ k ] = ⦃ ⦃ f ⦄ $ k ⦄
        ).
Lemma bindX_η_ctxt : forall `(f : mor Y X) `(g : mor Z _),
             ⦃ f ⦄ $ η $ g = f $ g.
  intros; rewrite <- comp_assoc, bindX_η. f_equal; autorewrite with monad; reflexivity.
Qed.
Lemma bindX_bind_ctxt : forall `(k : mor Z (T W))
                     `(f : mor W X)
                     `(g : mor Z _)
  ,
                               ⦃ f ⦄ $ [ k ] $ g = ⦃ ⦃ f ⦄ $ k ⦄ $ g.
Proof.
  intros; rewrite <- comp_assoc, bindX_bind. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite bindX_η @bindX_η_ctxt
     bindX_bind @bindX_bind_ctxt : monad.
     

Lemma bindX_norm : forall `(h : mor A X), ⦃ h ⦄ = ⦃ id ⦄ $ # T h.
  intros.
  autorewrite with monad.
  reflexivity.
Qed.




Context ( id_split : forall  Y Z , id (a := Y + Z) = i₁ || i₂).
Lemma sumeq `(f : mor (Y + Z) W)(g : mor (Y + Z) W) :
  i₁ ;; f = i₁ ;; g  ->
  i₂ ;; f = i₂ ;; g -> f = g.
Proof.
  intros.
  rewrite <- (idr f).
  rewrite <- (idr g).
  rewrite id_split.
  autorewrite with monad.
  congruence.
Qed.



(* diagramme manquant dans ceconfis3 03/09/2021 *)

Definition δ {X} : mor (T (S X)) (S (T X)) :=
  ⟦ # S η ⟧.

Definition O Y Z := (Z + Y)%o.
Definition Of `(f : mor A B) `(g : mor A' B') : mor (O A A') (O B B') := g + f.

(* Hint Rewrite (fun Y Z => eq_refl : @O Y Z = (Z + Y)%o) : monad. *)

Definition σ {A B} {m : monad} : mor (O A (m B)) (m (O A B)) :=
  (# m i₁ || i₂ ;; η).
  (* [id || i₂ ;;  η]. *)

Definition Oμ {A B} {m : monad} : mor (m (O A (m (O A B)))) (m (O A B)) :=
  [id || i₂ ;;  η].

Definition gμ {A B C} : mor (S (T (O A (O (S B) (S (T (O A (O B C))))))))
                            (S (T (O A (O B C)))).
  unfold O.
  refine (# S ( # T (id || _ || _)) ;; _).
  - refine (# S δ ;;  μ ;; # S μ ;; _ ).
    exact id.
    (* refine [ bind' (i₁ ;; i₁ ;; η ;; η || i₂ ;; i₁ ;; η ;; η || _)]. *)
    (* refine (# S i₂ ;; # S η). *)
  - exact (# S (i₂ ;; i₁ ;; η)).
  - exact (i₂ ;;η ;; η).
Defined.

Definition γST {A} {B} : mor (S (T (O (S (T A)) B))) (S (T (O A B))) .
  refine [ bind' ( _ || _) ].
  refine (i₁ ;; η ;; η ).
  refine (# S (# T (i₂))).
  Defined.

  

Lemma test (f : mor (S (T
                          (O
                             (S (T (S X)))
                             (O (S X)
                                (G
                                   (S (T (S X)))
                                   (S X)
                                )
                             )
                    )))
                    (S X)
           )   :
  # S (# T (Of (# S δ ;; μ )
               (Of id
                   (Gₘ (# S δ ;; μ) id ;;
                    h
                    (* ;; *)
                    (* # S (# T (Of id (Of (η (m := S) (x := X)) id)))  *)

               ))
               ) 
      ) ;; gμ ;; γST ;; # S (# T (a || id || id)) 
  ;; # S (bindX id) =
  γST ;; #S (# T (Of id (Of id (Gₘ (# S δ ;; μ) id
                                ;; h ;;
                                γST ;;
                                # S (# T (a || id || id) ;; ⦃ id ⦄ 
                                    )
                        ))
                 
               ;; (id || id || id))
             ;; δ ;; # S ⦃ id ⦄
            ) ;; μ.
  unfold gμ.
  unfold γST.
  unfold δ.
  unfold Of.
  unfold O.
  cbn.
  autorewrite with monad.
  unfold STS_ST.
  autorewrite with monad.
  try reflexivity.
  (* rewrite id_split. *)
  (* reflexivity. *)
  Abort.
   
  (* # S (# T ) = f. *)

  

(* fin diagramme manquant *)

(* diagramme ?1 (en bas a gauche) Figure 1 relative.pdf 17/09/2021 *)

Definition up {m : monad} {u v} : mor (u + m v)
                      (M m (u + v))
                    := η $ i₁ || (# m i₂) .

Definition LHS1 := 
   # S ( # T (Of id up ;; up ;; Oμ ;; # S (σ ;; # S σ) ;; μ
                            ;; # S (# T (id (a := X)|| id))) ;; δ 
                   ).

Definition Ld1  := LHS1 ;;# S (# S (# T ⦃ id ⦄)) .
Definition Rd1 :=                  # S (# T (Of id (Of id (# S ⦃ id ⦄)) ;;
                           (id || id || id)
                     )) ;; # S δ .


Lemma diag1   :  Ld1 = Rd1.
  unfold Ld1, LHS1, Rd1, up, σ, Oμ.
  unfold gμ, γST, δ, Of, O.
  cbn.
  autorewrite with monad.
  reflexivity.
  (* rewrite id_split. *)
  (* reflexivity. *)
  Qed.



(* diagramme ?2 *)
Lemma diag2 (f : mor (S (T (O (S (T (S X))) (O (S X) (S (T (O (S (T X)) (O X X))))))))
                     (S (T X))
            ) : # S(# T( Of id (Of id (γST ;; # S (# T (id || id || id)))))) ;; γST ;; LHS1 ;;
                  μ ;; # S μ 
                  =
                  # S (# T (Of (# S δ ;; μ) id)) ;; gμ ;; γST ;;
                  # S (# T (id || id || id)) .
  unfold LHS1, up, σ, Oμ.

  unfold gμ.
  unfold γST.
  unfold δ.
  unfold Of.
  unfold O.
  cbn.
  autorewrite with monad.
  reflexivity.
  Qed.


(* find diagramme manquant *)





(* Tentative hasardeuse d'augmenter le moteur de reecritures *)
    
Lemma bind'_nat_bindX : forall `(u : mor U X)
                       `(f : mor Z _)
                       (* `(g : mor W _) *)
          ,
            # S ⦃ u ⦄ $ ⟦ f ⟧ = # S ⦃ id ⦄ $ ⟦ # S (# T u)  $ f ⟧ .
Proof.
  intros.
  rewrite <- (bind'_nat (η $ u)  f ).
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.

Lemma monad_comp (M : monad) `(f : mor A B) `(g : mor B C) :
  # M (g $ f) = # M g $ # M f.
  autorewrite with monad.
  reflexivity.
Qed.

Lemma bind'_nat_bindX' : forall `(u : mor U X)
                       `(f : mor Z _)
                       `(g : mor _ W)
          ,
            # S (g $ ⦃ u ⦄) $ ⟦ f ⟧ = # S (g $ ⦃ id ⦄) $ ⟦ # S (# T u)  $ f ⟧ .
Proof.
  intros.
  rewrite <- (bind'_nat (η $ u)  f ).
  rewrite monad_comp.
  rewrite monad_comp.
  intros; rewrite <- comp_assoc. f_equal.
   autorewrite with monad; reflexivity.
Qed.

Lemma μ_mor' :
  Gₘ (# S (# T μ)) μ ;; Sa' a ⦃ id ⦄ = Sa' (Sa' a ⦃ id ⦄) (Sb' ⦃ id ⦄) ;; μ.
Proof.
  autorewrite with monad.
unfold STS_ST.
unfold O.
  autorewrite with monad.
  f_equal.
  f_equal.
  rewrite bind'_nat_bindX.
  autorewrite with monad.
  rewrite bind'_nat_bindX'.
  autorewrite with monad.
  rewrite id_split.
  (*
  [# S ⦃ a || id || id ⦄ $ ⟦ η $ η $ i₁ $ i₁ $ Gₘ μST id || η $ η $ i₁ $ i₂ || [⟦ # S (# T i₂) ⟧] ⟧] $
  ⟦ # S [η $ i₁ $ i₁ $ Gₘ (# S (# T [# S η])) id || η $ i₁ $ i₂ || η $ i₂ $ # S (# T [# S η])] $ h
    || # S (η $ i₁ $ i₂) || η $ η $ i₂ $ # S (# T [# S η]) ⟧ =
  [# S ⦃ id ⦄ $
   ⟦ [# S (η $ ⦃ a || id || id ⦄) $ ⟦ η $ η $ i₁ $ i₁ $ Gₘ [⟦ # S η ⟧] id || η $ η $ i₁ $ i₂ || [⟦ # S (η $ i₂) ⟧] ⟧] $
     h || # S η || # S η ⟧] $ ⟦ η $ η $ i₁ $ i₁ $ Gₘ [⟦ # S η ⟧] id || η $ η $ i₁ $ i₂ || [⟦ # S (η $ i₂) ⟧] ⟧

  [# S ⦃ a || id || id ⦄ $ ⟦ η $ η $ i₁ $ i₁ $ Gₘ μST id || η $ η $ i₁ $ i₂ || [# S (# T i₂) $ ⟦ id ⟧] ⟧] $
  ⟦ # S [η $ i₁ $ i₁ $ Gₘ (# S (# T [# S η])) id || η $ i₁ $ i₂ || η $ i₂ $ # S (# T [# S η])] $ h
    || # S (η $ i₁ $ i₂) || η $ η $ i₂ $ # S (# T [# S η]) ⟧ =
  [# S ⦃ id ⦄ $
   ⟦ [# S (η $ ⦃ a || id || id ⦄) $
      ⟦ η $ η $ i₁ $ i₁ $ Gₘ [⟦ # S η ⟧] id || η $ η $ i₁ $ i₂ || [# S (# T i₂) $ ⟦ # S η ⟧] ⟧] $ h || 
     # S η || # S η ⟧] $ ⟦ η $ η $ i₁ $ i₁ $ Gₘ [⟦ # S η ⟧] id || η $ η $ i₁ $ i₂ || [# S (# T i₂) $ ⟦ # S η ⟧] ⟧
*)
  apply sumeq.
  rewrite id_split.
  reflexivity.
  rewrite hax_ctxt_rel.
  autorewrite with monad.
  etransitivity;[|apply comp_assoc].
  etransitivity;[symmetry;apply comp_assoc|].

  f_equal.
  apply(f_equal (fun x => x $   h $ Gₘ [⟦ [# S η] ⟧] id )).
  rewrite comp_assoc.
  rewrite hμ_ctxt2.
End RelativeProp62.

(*

(*

Vieilles tentatives


 *)
Section RelativeDistrib.
  (* based on Observation 4.1 de Another characterization of no-iteration distributive laws *)

Context (T : monad).
Arguments T _%object_scope : extra scopes.
(* STY est une T-algebre (au sens de relative monads, def 2.11 de Altenkirch & cie) *)
Context (bind' : forall `(f : mor X (S (T Y))), mor (T X) (S (T Y))).
Notation "⟦ f ⟧" := (bind' f).

Context (bind'_η : forall `(f : mor X (S (T Y))),
             ⟦ f ⟧ $ η = f
        ).
Context (bind'_bind' : forall `(k : mor Z (T W))
                         `(f : mor W (S (T X))),
                               ⟦ f ⟧ $ [ k ] = ⟦ ⟦ f ⟧ $ k ⟧
        ).

(* forall h :  b → Ta, [η $ [ h ]] is an T-algebra map*)
Context (bind'_nat : forall `(h : mor b (T a))
                       `(f : mor Z _)
          ,
            [η $ [ h ]] $ ⟦ f ⟧ = ⟦ [η $ [ h ]] $ f ⟧
        ).

Notation λ := ⟦ [η $ η] ⟧.
(* diagramme 3 *)
Context (bind'_diag3 : forall a,
            λ $ [η $ η ] = (η (x := T a))
        ).
(* diagramme 4 *)
Context (bind'_diag4:  forall `(f : mor a (S b)),
            λ $ [η $ [f] ] = [⟦ [η $ η] ⟧ $ [η $ f]] $ λ
        ).


End.

Section RelativeOld.

Context (T : monad).
Arguments T _%object_scope : extra scopes.

(* loi distributive entre S et T <=> T se releve sur Kl(S) *)
Context (binddist : forall `(f : mor X (S (T Y))), mor (T X) (S (T Y))).

Notation "⟦ f ⟧" := (binddist f).

(* this means that it lifts the already existing bind *)
Context (binddist_η : forall `(f : mor X (T Y)),
             ⟦ f ;; η⟧ = [ f ] ;; η  
        ).

Hint Rewrite binddist_η : monad.
Corollary  binddist_η_alone : forall (X : ob) , ⟦ η (x := T X) ⟧ = η $ μ.
Proof.
  intro X.
  rewrite <- (idr η).
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite binddist_η_alone : monad.

(* bind of η is id, but in the kleisli *)
Corollary binddist_ηη : forall X, ⟦ η $ η (x := X) ⟧ = η.
  intro.
  autorewrite with monad.
  reflexivity.
Qed.

Context ( ηη_binddist : forall `(s : mor b (S (T c))) , (η ;; η ;; [ ⟦ s ⟧ ] = s)).

Corollary η_binddist : forall `(s : mor b (S (T c))) , (η ;;  ⟦ s ⟧  = s).
  intros.
  etransitivity; [ |apply ηη_binddist].
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite @η_binddist : monad.

Corollary η_binddist_ctxt : forall `(s : mor b (S (T c))) `(f : mor d b), (f ;; η ;;  ⟦ s ⟧ = f ;; s).
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @η_binddist_ctxt : monad.

Context (
    binddist_binddist : forall `(s : mor b (S (T c)))
                  `(s' : mor c (S (T d))),
      [⟦ s' ⟧] $ ⟦ s ⟧ = ⟦ [⟦ s' ⟧] $ s ⟧).
Hint Rewrite @binddist_binddist : monad.
Lemma 
    binddist_binddist_ctxt : forall `(s : mor b (S (T c)))
                               `(s' : mor c (S (T d)))
                               `(x : mor a (T b))
  ,
      [⟦ s' ⟧] $ ⟦ s ⟧ $ x = ⟦ [⟦ s' ⟧] $ s ⟧ $ x.
Proof.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @binddist_binddist_ctxt : monad.


(* Definition μST {X} : mor (S (T (S (T X)))) (S (T X)) := [⟦ id ⟧]. *)
Notation μST := [⟦ id ⟧].


Lemma binddist_eq `(f : mor X (S (T Y))) : ⟦ f ⟧ = [ ⟦ id ⟧ ] $ ⟦ η $ η $ f ⟧.
                                                              (* η $ # T f . *)
autorewrite with monad.
reflexivity.
Qed.
Lemma binddist_eq' `(f : mor X (S (T Y))) : ⟦ f ⟧ = # T f ;; ⟦ # S η⟧ ;; # S μ .
  autorewrite with monad.
Abort.

Lemma test `(f : mor X Y) : # T f ;; η = ⟦ η $ η $ f ⟧.
  autorewrite with monad.
  reflexivity.
Qed.
Lemma A' `(f : mor X (S (T Y)))  : ⟦ f ⟧ = ⟦ [η $ η] $ f ⟧ ;; [ ⟦ η ⟧ ].
  autorewrite with monad.
  reflexivity.
Qed.
Lemma A `(f : mor X (S (T Y))) : ⟦ f ⟧ = ⟦ [η $ η] $ f ⟧ ;; # S μ.
  etransitivity.
  apply A'.
  rewrite binddist_η_alone.
  reflexivity.
Qed.
Notation "'T_' f" := ( ⟦ [η $ η] $ f ⟧ ) (at level 30).

Lemma T_comp  `(f : mor X (S Y)) `(g : mor Y (S Z)) :
                                    T_ ([ g ] $ f) = [T_ g ] $ T_ f.
  autorewrite with monad.
  reflexivity.
Qed.
Lemma T_η  `(f : mor X Y) :
                                    T_ (η $ f) = η $ # T f.
  autorewrite with monad.
  reflexivity.
Qed.

Lemma B `(f : mor X (S (T Y))) : T_ f = # T f ;; T_ id.
  Proof.
    assert (hf : f = [id] $ η $ f).
{
    autorewrite with monad.
    reflexivity.
    }
etransitivity.
apply(f_equal (fun x => T_ x)).
apply hf.
rewrite T_comp.
rewrite T_η.
autorewrite with monad.
reflexivity.
  Qed.

Lemma incroyable `(f : mor X (S (T Y))) : ⟦ f ⟧ = ⟦ id ⟧ $ # T f.
Proof.
  rewrite (A f).
  rewrite (A id).
  rewrite (B f).
  autorewrite with monad.
  reflexivity.
Qed.

Lemma encore `(f : mor X (S Y)) : ⟦ η $ η $ f ⟧ = [ η $ f ] ;; ⟦ η $ η ⟧.
  Proof.
    autorewrite with monad.
    reflexivity.
    Qed.

Lemma binddist_eq' `(f : mor X (S (T Y))) : ⟦ f ⟧ = [ ⟦ id ⟧ ] $ η $ [ η $ f ].
                                                              (* η $ # T f . *)
autorewrite with monad.
reflexivity.
Qed.
Lemma binddist_eq' `(f : mor X (S (T Y)))  : [⟦ f ⟧] = [ ⟦ id ⟧ ] $ # S (# T f).
                                                              (* η $ # T f . *)
autorewrite with monad.
reflexivity.
Qed.
                                                                (* [η $ g]. *)

Definition STS_ST {X} : mor (S (T (S X))) (S (T X)) :=  [⟦ # S η ⟧].
Hint Rewrite (fun X => eq_refl : @STS_ST X = [⟦ # S η ⟧]) : monad.

(* Hint Rewrite (fun X => eq_refl : @μST X = [⟦ id ⟧]) : monad. *)

Context (h : forall X Y, mor (G (S (T X)) (S Y)) (S (T (G (S (T X)) Y + Y + S (T X))))).
Arguments h {X} {Y}.
Context (hax : forall X Y ,
            Gₘ μST id ;; @h X Y = h ;;
                                  # S (# T (Gₘ μST id + id + id)) 
                                  ;; # S ( # T (id + id + μST))).
Hint Rewrite hax : monad.
Lemma hax' X Y `(f : mor a (S Y)) :
    @h X Y $ Gₘ [# S (η (m := T))] f = Gₘ (# S η) f ;; h  ;;
                                  # S (# T (Gₘ STS_ST id + id + id))
                                  ;; # S (# T (id + id + STS_ST)) .
Admitted.
Hint Rewrite hax' : monad.

Definition bindST `(f : mor X (S (T Y))) : mor (S (T X)) (S (T Y)) :=
[⟦ id ⟧ $ # T f].

Lemma bindST_def `(f : mor X (S (T Y))) : bindST f = 
   # S (# T f)  ;;  μST .
  Abort.

Lemma hax_ctxt' : forall X Y `(f : mor a (S Y)),
    Gₘ μST f ;; @h X Y =
      # S [η $ i₁ $ i₁ $ Gₘ μST id || η $ i₁ $ i₂ || η $ i₂ $ μST] $ h $ Gₘ id f.
Proof.
  intros; rewrite <- (idl f).
  rewrite <- (idr μST).
  intros; rewrite <- Gcomp, <- comp_assoc.
  f_equal; rewrite hax. autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite hax_ctxt' : monad.

Context (hμ : forall X Y  , Gₘ id μ ;; @h X Y = h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST).
Hint Rewrite hμ : monad.

Corollary hμ_ctxt1 : forall X Y `(f : mor A _) , Gₘ f μ ;; @h X Y = Gₘ f id ;; h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST.
  intros; rewrite <- (idl f).
  rewrite <- (idr [id]).
  intros; rewrite <- Gcomp, <- comp_assoc.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite hμ_ctxt1 : monad.

(* ca peut boucler *)
Corollary hμ_ctxt2 : forall X Y `(f : mor A _)`(g : mor B _) , Gₘ f [ g ] ;; @h X Y = Gₘ f (# S g) ;; h
      ;; # S (# T ((h || # S (η $ i₁ $ i₂)) + id)) ;;
      #S (#T (id || η $ η $ i₂)) ;; μST.
  intros; rewrite <- (idl f).
  assert (hyp : [g] = # S g ;; [ id ]).
  {
    autorewrite with monad.
    reflexivity.
  }
  rewrite hyp.
  intros; rewrite <- Gcomp, <- comp_assoc.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad.
   reflexivity.
Qed.
(* Hint Rewrite hμ_ctxt2 : monad. *)

Context (hnat : forall `(f : mor Z X)`(g : mor W Y), @h X Y $ Gₘ (# S (# T f)) (# S g) =
                                               # S (# T (Gₘ (# S (# T f)) g + g + # S (# T f))) $ h 
        ).
Lemma hnat'_helper1 :
 forall `(f : mor Z X) Y, @h X Y $ Gₘ (# S (# T f)) id =
                                               # S (# T (Gₘ (# S (# T f)) id + id + # S (# T f))) $ h .
  intros.
  rewrite <- hnat.
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite @hnat'_helper1 : monad.

Definition γsST  {a b} : mor (S (T (a + (S (T b)))))
                      (S (T (a + b))) :=
   # S (# T (η $ η $ i₁ || # S (# T i₂)) ) ;; μST .
(* Lemma yop a b : @γsST a b =  *)
(*    # S (# T (η $ η $ i₁ || # S (# T i₂)) ) ;; μST . *)
(* autorewrite with monad. *)


(*
Definition Sa'
           `(a : mor (G (S X) X) X)
           (b : mor (T X) X)
  : mor (G (S (S X)) (S X)) (S X):=
  Gₘ μ id ;; Gₘ (#S η) id ;; h ;; γsST ;;
  # S (# T ( Gₘ (# S b) id + id + id)) ;; # S (# T (a || id || id)) ;;
        # S b.

Lemma Sa'_simpl 
           `(a : mor (G (S X) X) X)
           (b : mor (T X) X) :
  Sa' a b =
  [# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $ h $ Gₘ [# S η] id.
  unfold Sa',γsST.
  autorewrite with monad.
  reflexivity.
Qed.
*)
Definition Sa'
           `(a : mor (G (S (T X)) X) X)
           (b : mor (T X) X)
  : mor (G (S (T (S X))) (S X)) (S X):=
  Gₘ STS_ST id ;; h ;; γsST ;;
  # S (# T (a || id || id)) ;;
        # S b.

Lemma Sa'_simpl 
           `(a : mor (G (S (T X)) X) X)
           (b : mor (T X) X) :
  Sa' a b =
   [# S (b $ [η $ a || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $ h $ Gₘ [⟦ # S η ⟧] id.
  (* Gₘ STS_ST id ;; h ;; γsST ;; *)
  (* # S (# T (a || id || id)) ;; *)
  (*       # S b. *)
  unfold Sa',γsST.
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite @Sa'_simpl : monad.
          
Definition Sb'
           `(b : mor (T X) X)
  : mor (T (S X)) (S X) :=
   ⟦ # S η ⟧ ;; # S b.

Lemma Sb'_simpl `(b : mor (T X) X) :
  Sb' b = 
   ⟦ # S η ⟧ ;; # S b.
  reflexivity.
Qed.
Hint Rewrite @Sb'_simpl : monad.

Context (X : ob)
        (* (a : mor (G (S X) X) X) *)
        (a : mor (G (S (T X)) X) X)
        (b : mor (T X) X).

Context (bη : b $ η = id).

Hint Rewrite bη : monad.
Lemma bη_ctxt `(f : mor A X) : b $ η $ f = f.
  intros; rewrite <- comp_assoc. f_equal; autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @bη_ctxt : monad.

Context (bμ : b $ # T b = b $ μ).
Hint Rewrite bμ : monad.

Corollary bbind_ctx1 : forall `(f : mor Y (T X)),
    b $ # T (b $ f) = b $ [ f ].
  intros.
  assert (hyp : # T (b $ f) = # T b $ # T f).
  { autorewrite with monad. reflexivity. }
  rewrite hyp.
  intros; rewrite <- comp_assoc. rewrite bμ. autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @bbind_ctx1 : monad.

Corollary bbind_ctxt_ctx2 : forall `(f : mor Y (T X)) `(g : mor Z (T Y)),
    b $ # T (b $ f) $ g = b $ [ f ] $ g.
  intros; rewrite <- comp_assoc.  
  rewrite bbind_ctx1.
  autorewrite with monad.
  reflexivity.
Qed.
Hint Rewrite @bbind_ctxt_ctx2 : monad.

Corollary bbind_ctxt_ctx3 : forall `(g : mor Z (T (T X))),
    b $ # T b $ g = b $ μ $ g.
  intros; rewrite <- comp_assoc.
  rewrite bμ.
  autorewrite with monad; reflexivity.
Qed.
Hint Rewrite @bbind_ctxt_ctx3 : monad.

(* Lemma helper1 `(f : mor Z X) : b $ ( η $ f || η || η) = (f || id || id). *)
(*   etransitivity; [ | apply idl]. *)
(*   etransitivity; [ | ] *)
(* Lemma test f : (b $ [η $ a $ Gₘ (# S b) id || η || η]) = f. *)
(*   rewrite <- bbind_ctx1. *)
(*   autorewrite with monad. *)
(*   rewrite <- bbind_ctx1. *)

(*
Definition r1 :=
  [[# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
   ⟦ id ⟧ $ [η $ h || η $ # S (η $ i₁ $ i₂) || η $ η $ η $ i₂]] $ h $ Gₘ [[# S η]] id =
  [[# S b $
    ⟦ # S η ⟧ $
    [η $
     [# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
     h $ Gₘ [# S (η $ b) $ ⟦ # S η ⟧] id || η || η]] $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
  h $ Gₘ [# S η] id
.

Definition r_sans_hax := 
  [[# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
   ⟦ id ⟧ $ [η $ h || η $ # S (η $ i₁ $ i₂) || η $ η $ η $ i₂]] $ h $ Gₘ [[# S η]] id =
  [[# S b $
    ⟦ # S η ⟧ $
    [η $
     [# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
     h $ Gₘ [# S (η $ b) $ ⟦ # S η ⟧] id || η || η]] $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
  h $ Gₘ [# S η] id
.
*)

   


(* Check (eq_refl :r1 = r_sans_hax). *)
Lemma μ_mor' :
  Gₘ (# S (# T μ)) μ ;; Sa' a b = Sa' (Sa' a b) (Sb' b) ;; μ.
Proof.
  autorewrite with monad.
  rewrite hμ_ctxt2.
  (*
  [[# S (b $ [η $ a || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
   ⟦ id ⟧ $ [η $ h || η $ # S (η $ i₁ $ i₂) || η $ η $ η $ i₂]] $ h $ Gₘ [⟦ # S η ⟧ $ # T μ] id =
  [[# S b $
    ⟦ # S η ⟧ $
    [η $ [# S (b $ [η $ a || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $ h $ Gₘ [⟦ # S η ⟧] id || η
     || η]] $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $ h $ Gₘ [⟦ # S η ⟧] id
  *)
  Print Rewrite HintDb  monad.
  f_equal.
  f_equal.
  (*
  [# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $ h $ Gₘ [[# S η]] μ =
  [[# S b $
    ⟦ # S η ⟧ $
    [η $
     [# S (b $ [η $ a $ Gₘ (# S b) id || η || η]) $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
     h $ Gₘ [# S (η $ b) $ ⟦ # S η ⟧] id || η || η]] $ ⟦ id ⟧ $ [η $ η $ η $ i₁ || η $ # S (# T i₂)]] $
  h $ Gₘ [# S η] id

  *)
  reflexivity.
  rewrite <- bbind_ctx1.
  rewrite !mor_copairm, !bη_ctxt, !bη.
  autorewrite with monad.
  rewrite <- bbind_ctx1.
  f_equal.
  reflexivity.
  rewrite bη_ctxt.
  rewrite @η_bind_ctxt.
  rewrite @bbind.
  rewrite ?bind_bind_ctxt, ?@η_bind, ?@bind_bind, ?@bind_eta, ?@copairm_i₂_ctxt,
          ?@copairm_i₁_ctxt, ?@mor_copairm_ctxt, ?@copairm_i₂.
  rewrite ?hμ, ?hax_ctxt', ?hax.
  rewrite ?@binddist_binddist_ctxt,
  ?@binddist_binddist,
  ?@η_binddist_ctxt,
  ?@η_binddist,
  ?binddist_η_alone,
  ?binddist_binddist.
rewrite  ?@bbind_ctxt
  , ?@bbind.
  , ?@bη_ctxt.
  , ?bη.
  , ?@Sb'_simpl
  , ?@Sa'_simpl.
  , ?hμ
  , ?hax_ctxt'
  , ?hax.
  , ?@binddist_binddist_ctxt
  , ?binddist_binddist
  , ?@η_binddist_ctxt
  , ?@η_binddist
  , ?binddist_η_alone.
  , ?binddist_η
  , ?Gid
  , ?@Gcomp_ctxt
  , ?Gcomp
  , ?η_bind_ctxt
  , ?bind_bind_ctxt
  , ?η_bind
  , ?bind_bind
  , ?bind_eta
  , ?@copairm_i₂_ctxt
  , ?@copairm_i₁_ctxt
  , ?@mor_copairm_ctxt
  , ?copairm_i₂
  , ?copairm_i₁
  , ?mor_copairm
  , ?@summ_def
  , ?idr
  , ?idl
  , ?comp_assoc.
  (*
rewrite  ?@bbind_ctxt
  , ?@bbind
  , ?@bη_ctxt
  , ?bη
  , ?@Sb'_simpl
  , ?@Sa'_simpl
  , ?hμ
  , ?hax_ctxt'
  , ?hax
  , ?@binddist_binddist_ctxt
  , ?binddist_binddist
  , ?@η_binddist_ctxt
  , ?@η_binddist
  , ?binddist_η_alone
  , ?binddist_η
  , ?Gid
  , ?@Gcomp_ctxt
  , ?Gcomp
  , ?η_bind_ctxt
  , ?bind_bind_ctxt
  , ?η_bind
  , ?bind_bind
  , ?bind_eta
  , ?@copairm_i₂_ctxt
  , ?@copairm_i₁_ctxt
  , ?@mor_copairm_ctxt
  , ?copairm_i₂
  , ?copairm_i₁
  , ?mor_copairm
  , ?@summ_def
  , ?idr
  , ?idl
  , ?comp_assoc.
*)


  repeat rewrite bη_ctxt.
  autorewrite with monad.
  Print Rewrite HintDb monad.
  autorewrite with monad.
  autorewrite with monad.
  f_equal.
  reflexivity.
  unfold Sa, γs.
  cbn.
  autorewrite with monad.
  reflexivity.
Qed.


*)
