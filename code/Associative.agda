module Associative where

open import Algebra.FunctionProperties
open import Data.Bool
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

F : Set → Bool → Set
F A = λ b → if b then A else ⊤

G : Set → Set
G A = Σ Bool (F A)

-- lifting of functions
liftOp2 : {A : Set} → Op₂ A → Op₂ (G A)
liftOp2 f (true , ax) (true , ay) = true , f ax ay
liftOp2 f (true , ax) (false , ay) = true , ax
liftOp2 f (false , ax) (true , ay) = true , ay
liftOp2 f (false , ax) (false , ay) = false , tt

-- lifting of relations
liftRel : {A : Set} → (A → A → Set) → (G A → G A → Set)
liftRel R (true , b1) (true , b2) = R b1 b2
liftRel R (a1 , b1) (a2 , b2) = a1 ≡ a2


-- assoc f implies assoc lift f

assoc-f-implies-assoc-lift-f :
  { A : Set } →
  { _≈_ : A → A → Set } →
  { p : Reflexive _≈_ } →
  ( f : A → A → A ) → 
  Associative _≈_ f →
  Associative (liftRel _≈_) (liftOp2 f)
assoc-f-implies-assoc-lift-f f assoc-f (true , v1) (true , v2) (true , v3) = assoc-f v1 v2 v3
assoc-f-implies-assoc-lift-f {p = p} f assoc-f (true , v1) (true , v2) (false , v3) = p
assoc-f-implies-assoc-lift-f {p = p} f assoc-f (true , v1) (false , v2) (true , v3) = p
assoc-f-implies-assoc-lift-f {p = p} f assoc-f (true , v1) (false , v2) (false , v3) = p
assoc-f-implies-assoc-lift-f {p = p} f assoc-f (false , v1) (true , v2) (true , v3) = p
assoc-f-implies-assoc-lift-f {p = p} f assoc-f (false , v1) (true , v2) (false , v3) = p
assoc-f-implies-assoc-lift-f {p = p} f assoc-f (false , v1) (false , v2) (true , v3) = p
assoc-f-implies-assoc-lift-f f assoc-f (false , v1) (false , v2) (false , v3) = refl

-- product of relations
liftProd : ∀ {ℓ} → {A B : Set} → Rel A ℓ → Rel B ℓ → Rel (A × B) ℓ
liftProd P Q (a1 , b1) (a2 , b2) = P a1 a2 × Q b1 b2

liftRefl : ∀ {ℓ} → {A B : Set} 
         → (P : Rel A ℓ) → Reflexive P
         → (Q : Rel B ℓ) → Reflexive Q
         → Reflexive (liftProd P Q)
liftRefl P refl-P Q refl-Q = refl-P , refl-Q

liftFun : ∀ {A B : Set} → Op₂ A → Op₂ B → Op₂ (A × B)
liftFun f g (a1 , b1) (a2 , b2) = f a1 a2 , g b1 b2

-- assoc f and assoc g implies assoc (f x g)
assoc-lifts-to-pairs : ∀ {ℓ A B}
  → (_≈₁_ : Rel A ℓ) (f : Op₂ A) → Associative _≈₁_ f
  → (_≈₂_ : Rel B ℓ) (g : Op₂ B) → Associative _≈₂_ g
  → Associative (liftProd _≈₁_ _≈₂_) (liftFun f g)
assoc-lifts-to-pairs _≈₁_ f assoc-f _≈₂_ g assoc-g =
  λ x y z → assoc-f (proj₁ x) (proj₁ y) (proj₁ z) , assoc-g (proj₂ x) (proj₂ y) (proj₂ z)


-- is there a useful lifting of associative functions to sums?
-- ie., if f : Op₂ A and g : Op₂ B are associative, is there
-- an associative extension h (f, g) : Op₂ (A ⊎ B) ?
-- I don't think so, because it is unclear how to define
-- h (inj₁ a) (inj₂ b)
-- One possibility is, given identity elements ea : A and eb : B,
-- to inject everything into pairs
-- Inject : {A B : Set} → A → B → A ⊎ B → A × B
-- Inject ea eb (inj₁ a) = a , eb
-- Inject ea eb (inj₂ b) = ea , b
-- or even nested pairs
-- InjectN : {A B : Set} → A ⊎ B → (A ⊎ B) ⊎ (A × B)
-- InjectN a-or-b = inj₁ a-or-b

-- liftSum : (f : Op₂ A) (g : Op₂ B) → Op₂ ((A ⊎ B) ⊎ (A × B))
-- liftSum f g x y = ...
-- liftSum f g (inj₁ (inj₁ a1)) (inj₁ (inj₁ a2)) = (inj₁ (inj₁ (f a1 a2)))
-- liftSum f g (inj₁ (inj₁ a1)) (inj₁ (inj₂ b2)) = (inj₂ (a1 , b2))
-- liftSum f g (inj₁ (inj₂ b1)) (inj₁ (inj₁ a2)) = (inj₂ (a2 , b1))
-- liftSum f g (inj₁ (inj₂ b1)) (inj₁ (inj₂ a2)) = (inj₁ (inj₂ (g b1 b2)))
-- .... and 12 more cases

-- this construction gives rise to an associative function
-- but it is rather tedious


ntimes : {A : Set} → ℕ → (f : Op₂ A) → (e : A) → A → A
ntimes zero f e a = e
ntimes (suc n) f e a = f a (ntimes n f e a)

ntimesf : {A : Set} → ℕ → (f : Op₂ A) → (e : A) → Op₂ A
ntimesf n f e x y = f (ntimes n f e x) (ntimes n f e y)




open ≡-Reasoning

-- should be predefined somewhere
symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

fntimes-comm : {A : Set} → (n : ℕ) → (f : Op₂ A) → (e : A) → (x : A)
             → Associative _≡_ f → Identity _≡_ e f
             → f (ntimes n f e x) x ≡ f x (ntimes n f e x)
fntimes-comm zero f e x assoc-f ident-e = 
  begin 
    f e x
  ≡⟨ (proj₁ ident-e) x  ⟩
    x
  ≡⟨ symm (proj₂ ident-e x) ⟩
    f x e
  ∎
fntimes-comm (suc n) f e x assoc-f ident-e = 
  begin 
    f (f x (ntimes n f e x)) x
  ≡⟨ assoc-f x (ntimes n f e x) x ⟩
    f x (f (ntimes n f e x) x)
  ≡⟨ cong (f x) (fntimes-comm n f e x assoc-f ident-e) ⟩
    f x (f x (ntimes n f e x))
  ∎

{-
-- unfortunately, this does not hold!
assoc-nx+ny : {A : Set} → (n : ℕ) → (f : Op₂ A) → (e : A)
  → Associative _≡_ f → Identity _≡_ e f → Associative _≡_ (ntimesf n f e)
assoc-nx+ny n f e assoc-f ident-e x y z = ?
-}

fext : {A : Set} → (f : Op₂ A) → (b : A) → Op₂ A
fext f b x y = f b (f x y)

assoc-fext-b : {A : Set} (f : Op₂ A) (b : A)
  → Associative _≡_ f → Commutative _≡_ f → Associative _≡_ (fext f b)
assoc-fext-b f b assoc-f comm-f x y z =
  begin 
    f b (f (f b (f x y)) z) 
  ≡⟨ cong (λ □ → f b (f □ z)) (symm (assoc-f b x y)) ⟩
    f b (f (f (f b x) y) z)
  ≡⟨ cong (λ □ → f b □) (assoc-f (f b x) y z) ⟩
    f b (f (f b x) (f y z))
  ≡⟨ cong (λ □ → f b (f □ (f y z))) (comm-f b x) ⟩
    f b (f (f x b) (f y z))
  ≡⟨ cong (λ □ → f b □) (assoc-f x b (f y z)) ⟩
    f b (f x (f b (f y z)))
  ∎
