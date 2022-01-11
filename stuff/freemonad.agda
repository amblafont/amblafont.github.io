{-# OPTIONS --rewriting --type-in-type #-}
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

id : {X : Set} → X → X
id x = x

coe : ∀ {i} {A B : Set i} (p : A ≡ B) → A → B
coe refl x = x

coe! : ∀ {i} {A B : Set i} (p : A ≡ B) → B → A
coe! refl x = x

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → (x ≡ y → f x ≡ f y)
ap f refl = refl

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 80 _∙_ -- _∙'_

_∙_ : ∀ {i}{A : Set i}{x y z : A}
  → (x ≡ y → y ≡ z → x ≡ z)
refl ∙ q = q

_⁻¹ : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

infix 5 _⁻¹

module _ {i}{A : Set i}{j} {P : A → Set j} {f g : (x : A) → P x} where
  postulate
  -- ou alors on pourrait demander simplement que les foncteurs postules
  -- par la suite sont compatibles avec l'egalite pointwise
    λ= : (∀ a → f a ≡ g a) → f ≡ g


data _∐_ : (A : Set) → (B : Set) → Set where
   inl : ∀ {A}{B} → A → A ∐ B
   inr : ∀ {A}{B} → B → A ∐ B

copair : ∀ {A}{B} → {C : Set} → (A → C) → (B → C) → (A ∐ B) → C
copair f g (inl x) = f x
copair f g (inr x) = g x


-- C'est notre Sigma
postulate
   F : Set → Set
   Ff : ∀ {A}{B} → (f : A → B) → F A → F B
   F∘ : ∀ {A}{B}{C} → (f : B → C)
        → (g : A → B) → ∀ x → Ff f (Ff g x) ≡ Ff (λ z → f (g z)) x
   Fid : ∀ {A} → (x : F A) → Ff (λ z → z) x ≡ x
{-# REWRITE F∘ #-}
{-# REWRITE Fid #-}

postulate
   S : Set → Set
   ret : {X : Set} →  X → S X
   ind : {X : Set} → F (S X) → S X
postulate
    -- this states (in the indexed way) that any X+F-algebra morphism 
    -- R → S X has a section, which is equivalent to
    -- S X being initial 
   SX-ind : {X : Set} → (P : S X → Set)
            → (∀ x →  P (ret x))
            → (( f : F (Σ (S X) P)) → P (ind (Ff fst f))) 
            → ∀ x → P x
   SX-ind-ret : ∀ {X}P Pret Pind x → SX-ind {X} P Pret Pind (ret x) ≡ Pret x 
   SX-ind-ind : ∀ {X}P Pret Pind x → SX-ind {X} P Pret Pind (ind x) ≡
      Pind (Ff (λ z → (z , SX-ind P Pret Pind z)) x) 

{-# REWRITE SX-ind-ret #-}
{-# REWRITE SX-ind-ind #-}

SX-rec : ∀ {X Y}(a : F Y → Y)(x : X → Y) → S X → Y
SX-rec {X}{Y} a x = SX-ind (λ _ → Y) x (λ f → a (Ff snd f) )

bind : ∀ {X}{Y} → (f : X → S Y) → S X → S Y
bind {X}{Y} f = SX-rec ind f

Sf : ∀ {X}{Y} → (f : X → Y) → S X → S Y
Sf f z = bind (λ x → ret (f x)) z

Sid : ∀ {X} z → Sf (id {X}) z ≡ z
Sid  = SX-ind _ (λ x → refl) (λ f → ap (λ u → ind (Ff u f)) (λ= snd))

μ : ∀ {X} → S (S X) → S X
μ  = bind id

μμ : ∀ {X : Set} z → μ {X} (μ z) ≡ μ (Sf μ z)
μμ {X} = SX-ind _ (λ x → refl) λ f → ap (λ u → ind (Ff u f)) (λ= snd)

postulate
  ℸ : Set → Set → Set
  ℸf : ∀ {A}{B}{A'}{B'} → (f : A → B) → (g : A' → B') → ℸ B A' → ℸ A B'
  ℸid : ∀ {A}{B} → ℸf (id {A}) (id {B}) ≡ id
  ℸf∘ : ∀ {A B C A' B' C' : Set} →
          (f : A → B) →
          (g : B → C) →
          (f' : A' → B') →
          (g' : B' → C') →
          ∀ x →
          ℸf f g' (ℸf g f' x) ≡ ℸf (λ z → g (f z)) (λ z → g' (f' z)) x

-- loi homogene
  b : ∀ {X}{Y} → F (Y × ℸ (S X) Y) → ℸ X (S (Y ∐ X))
  b-nat : ∀ {X X' Y Y' : Set}(f : X' → X)(g : Y → Y')
             (z : F (Y × ℸ (S X) Y) ) → 
          ℸf id (Sf (copair inl λ x → inr (f x))) ( b {X'}{Y'} (Ff (λ x → (g (fst x)) , ℸf (Sf f) g (snd x)) z))
            ≡ ℸf f (Sf (copair (λ x → inl (g x)) inr)) (b {X}{Y} z)

{-# REWRITE ℸf∘ #-}
{-# REWRITE ℸid #-}

-- on specialise f a id
b-nat-fid : ∀ {X Y Y' : Set}(g : Y → Y')
            (z : F (Y × ℸ (S X) Y) ) → 
        ( b {X}{Y'} (Ff (λ x → (g (fst x)) , ℸf (id {S X}) g (snd x)) z))
          ≡ ℸf id (Sf (copair (λ x → inl (g x)) inr)) (b {X}{Y} z)
b-nat-fid g z =  ap (λ u → b (Ff (λ a → g (fst a) , ℸf u g (snd a)) z))
     -- (λ= {!←!})
     (λ= Sid ⁻¹) ∙
      
      ap (λ u → ℸf id u (b (Ff (λ x → g (fst x) , ℸf (Sf id) g (snd x)) z)))
        { id }
        { Sf (copair inl (λ x → inr (id x))) }
        (λ= (SX-ind _ ( λ { (inl r) → refl ; (inr r) → refl})
          λ u → ap (λ m → ind (Ff m u)) (λ= snd) )) 
        ∙ b-nat id g z

-- on precompose par f
b-nat-fid-pre : ∀ {X Y Y' A : Set}(f : S X → A)(g : Y → Y')
            (z : F (Y × ℸ A Y) ) → 
        ( b {X}{Y'} (Ff (λ x → (g (fst x)) , ℸf f g (snd x)) z))
          ≡ ℸf id (Sf (copair (λ x → inl (g x)) inr)) (b {X}{Y} (Ff (λ x → fst x , ℸf f id (snd x)) z))
b-nat-fid-pre f g z = b-nat-fid g (Ff (λ x → fst x , ℸf f id (snd x)) z)

-- on specialise g a id
b-nat-gid : ∀ {X X' Y : Set}(f : X' → X)
  (z : F (Y × ℸ (S X) Y) ) → 
  ℸf id (Sf (copair inl λ x → inr (f x))) ( b {X'}{Y} (Ff (λ x → (fst x) , ℸf (Sf f) id (snd x)) z))
  ≡ ℸf f id (b {X}{Y} z)
b-nat-gid f z =  b-nat f id z ∙ ap (λ u → ℸf f u (b z))
   (λ= (SX-ind _ ( λ { (inl r) → refl ; (inr r) → refl})
     λ u → ap (λ m → ind (Ff m u)) (λ= snd) ))

-- on postcompose par g
b-nat-gid-post : ∀ {X X' Y A : Set}(f : X' → X) (g : S (Y ∐ X) → A)
  (z : F (Y × ℸ (S X) Y) ) → 
  ℸf id (λ y → g (Sf (copair inl λ x → inr (f x)) y)) ( b {X'}{Y} (Ff (λ x → (fst x) , ℸf (Sf f) id (snd x)) z))
  ≡ ℸf f g (b {X}{Y} z)
b-nat-gid-post f g z = ap (ℸf id g) (b-nat-gid f z)

-- ℸ (S X) - × id se releve en un foncteur $(Σ+X)-alg→Σ-alg$
ℸa : ∀ {X Y : Set}(x : X → Y)(a : F Y → Y) → F (Y × ℸ (S X) Y) → ℸ (S X) Y
ℸa {X}{Y} x a z = ℸf id (SX-rec a (copair id (SX-rec a x)))
    (b (Ff (λ m → (fst m , ℸf (μ {X}) id (snd m))) z))


-- fonctorialite du relevement: action sur les morphismes
ℸaf : ∀ {X Y Y' : Set}(f : Y → Y')(x : X → Y)(a : F Y → Y)(a' : F Y' → Y')
  → (∀ z → a' (Ff f z) ≡ f (a z))
  → ∀ z → ℸf id f (ℸa x a z) ≡ ℸa (λ z → f (x z)) a' (Ff (λ a → f (fst a) , ℸf id f (snd a)) z)
ℸaf {X}{Y}{Y'} f x a a' ha z = 
   ap (λ u → ℸf id u (b (Ff (λ m → fst m , ℸf μ id (snd m)) z)))
     (λ= (SX-ind _ helper1
       λ u → 
             (ha _ ⁻¹) ∙ ap (λ v → a' (Ff v u)) (λ= snd))
       )
       ∙
    ap (ℸf id (SX-rec a' (copair id (SX-rec a' (λ c → f (x c))))))
     (b-nat-fid-pre μ f z ⁻¹ )

  where
   helper1 : (x₁ : Y ∐ S X) →
      f (copair id (SX-rec a x) x₁) ≡
      copair id (SX-rec a' (λ c → f (x c)))
      (copair (λ x₂ → inl (f x₂)) inr x₁)
   helper1 (inl x) = refl
   helper1 (inr y) = SX-ind (λ y → f (SX-rec a x y) ≡ SX-rec a' (λ c → f (x c)) y)
      (λ x → refl)
      (λ u → 
      (ha _ ⁻¹) ∙
      ap (λ v → a' (Ff v u)) (λ= snd)
      ) y

ℸa-μ : ∀ {X : Set} 
       → ∀ (z : F (S X × ℸ (S (S X)) (S X)) ) → ℸf (μ {S X}) id (ℸa id ind z) ≡
       ℸa μ ind
        (Ff (λ a → (fst a) , ℸf μ id (snd a)) z)
ℸa-μ {X} z  =
   (
   (b-nat-gid-post
       (λ z₁ → SX-ind (λ _ → S (S X)) id (λ f → ind (Ff snd f)) z₁)
       (λ z₁ →
         SX-ind (λ _ → S X) (copair id (SX-rec ind id))
         (λ f → ind (Ff snd f)) z₁)
         (Ff (λ z₁ → fst z₁ , ℸf (λ b₁ → (μ b₁)) id (snd z₁)) z)
         -- ?
         -- (Ff (λ z₁ → fst z₁ , ℸf (λ b₁ → μ (Sf μ b₁)) id (snd z₁)) z)
       ⁻¹)
   ∙
   
   ap
     (λ u →
        ℸf id
        (λ y →
           SX-ind (λ _ → S X) (copair id (SX-rec ind id)) (λ f → ind (Ff snd f))
           (Sf
            (copair inl
             (λ x →
                inr (SX-ind (λ _ → S (S X)) (λ x₁ → x₁) (λ i → ind (Ff snd i)) x)))
            y))
        (b (Ff u z)))
     (λ= (λ a → ap (λ u → fst a , ℸf (λ b → (u b) ) id (snd a))
     (λ= (λ b → μμ b ⁻¹))))
   ∙
    
    ap (λ u → ℸf id u (b
       (Ff
        (λ z₁ →
           fst z₁ ,
           ℸf
           (λ z₂ →
              SX-ind (λ _ → S (S X)) (λ x → x) (λ i → ind (Ff snd i))
              (SX-ind (λ _ → S (S (S X))) (λ x → x) (λ i → ind (Ff snd i)) z₂))
           (λ z₂ → z₂) (snd z₁))
        z)))
        (λ= helper ⁻¹)
   )
   where
    helper : ∀ y →    SX-rec ind (copair id (SX-rec ind μ)) y
        ≡ (
         SX-ind (λ _ → S X) (copair id (SX-rec ind id)) (λ f → ind (Ff snd f))
         (Sf
          (copair inl
           (λ x →
              inr (SX-ind (λ _ → S (S X)) (λ x₁ → x₁) (λ i → ind (Ff snd i)) x)))
          y))
    helper2 : (x : S X ∐ S (S (S X))) →
      SX-rec ind (copair id (SX-rec ind μ)) (ret x) ≡
      copair id (SX-rec ind id)
      (copair inl
       (λ x₁ →
          inr (SX-ind (λ _ → S (S X)) (λ x₂ → x₂) (λ i → ind (Ff snd i)) x₁))
       x)

    helper = SX-ind _
       helper2
       λ u → ap (λ y → ind (Ff y u)) (λ= snd)

    helper2 (inl x) = refl
    helper2 (inr x) =
     SX-ind
       (λ x → SX-rec ind (copair id (SX-rec ind μ)) (ret (inr x)) ≡ μ (Sf μ x))
       (λ x₁ → refl)
       (λ f → ap (λ u → ind (Ff u f)) (λ= snd)) x
        ∙
        ((μμ x) ⁻¹)  

Sa : ∀{X} → (a : X → ℸ (S X) X) → S X → ℸ (S (S X)) (S X)
Sa {X} a =
   SX-ind (λ _ → ℸ (S (S X)) (S X)) 
   (λ x → ℸf μ ret (a x) )
    (ℸa id ind )


mul-ℸ-mor : ∀ {X}(a : X → ℸ (S X) X) → ∀ x →
     ℸf μ id (Sa a (μ x)) ≡ ℸf id μ (Sa (Sa a) x)
mul-ℸ-mor {X} a =
   SX-ind _
   (λ x → refl)
   (λ f → ℸa-μ (Ff
                  (λ z →
                    SX-ind (λ _ → S X) id (λ f₁ → ind (Ff snd f₁)) (fst z) ,
                    SX-ind (λ _ → ℸ (S (S X)) (S X))
                    (λ x → ℸf (SX-ind (λ _ → S X) id (λ i → ind (Ff snd i))) ret (a x))
                    (ℸa (λ x → x) ind)
                    (SX-ind (λ _ → S X) id (λ f₁ → ind (Ff snd f₁)) (fst z)))
                  f)

               ∙ ap (λ g → ℸa μ ind (Ff g f))
               (λ= (λ a →    ap ((_,_ (μ {X} (fst a))) ) (snd a)  ))
               ∙ ( ( (ℸaf ((λ z → SX-ind (λ _ → S X) id (λ i → ind (Ff snd i)) z)) id ind ind
                  (λ z → refl)
                  (Ff (λ z → (fst z) ,
                   
                                       SX-ind (λ _ → ℸ (S (S (S X))) (S (S X)))
                    (λ x →
                        ℸf (SX-ind (λ _ → S (S X)) id (λ i → ind (Ff snd i))) ret
                        (SX-ind (λ _ → ℸ (S (S X)) (S X))
                        (λ x₁ →
                            ℸf (SX-ind (λ _ → S X) (λ x₂ → x₂) (λ i → ind (Ff snd i))) ret
                            (a x₁))
                        (ℸa id ind) x))
                    (ℸa id ind) (fst z)
                     ) f )
                   ⁻¹ )
                  )  ))
