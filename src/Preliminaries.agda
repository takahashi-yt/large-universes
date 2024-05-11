{-# OPTIONS --without-K #-}

module Preliminaries where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality


-- the empty type ⊥

data ⊥ : Set where

⊥elim : {ℓ : Level} → (C : ⊥ → Set ℓ) → (x : ⊥) → C x
⊥elim C ()


-- the eliminator for the unit type

⊤elim : {ℓ : Level} → (C : ⊤ → Set ℓ) → C tt → (x : ⊤) → C x
⊤elim C a tt = a


-- the eliminator for the boolean type

Boolelim : {ℓ : Level} → (C : Bool → Set ℓ) → C true → C false →
           (x : Bool) → C x
Boolelim C a b false = b
Boolelim C a b true = a


-- the eliminator for Id

≡elim : {a : Level} → {A : Set a} → (D : (x y : A) (p : x ≡ y) → Set a) →
        ((x : A) → D x x refl) → (x y : A) → (p : x ≡ y) → D x y p
≡elim D a x .x refl = a x


-- application of a function as a functor

ap : {a b : Level} {A : Set a} {B : Set b} → (f : A → B) → {x y : A} →
  x ≡ y → f x ≡ f y
ap f refl = refl


-- transport

transp : {a b : Level} {A : Set a} (P : A → Set b) → {x y : A} →
         x ≡ y → P x → P y
transp P refl = λ c → c


-- dependent map

apd : {a b : Level} {A : Set a} {B : A → Set b} → (f : (x : A) → B x) → {x y : A} →
  (p : x ≡ y) → transp B p (f x) ≡ f y
apd f refl = refl


-- ≡ is an equivalence relation

≡sym : {a : Level} {A : Set a} {x y : A} → x ≡ y → y ≡ x
≡sym refl = refl

≡trans : {a : Level} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡trans {a}{A}{x}{y}{z} p q = ≡trans-lem x y p z q
  where
  ≡trans-lem : (x y : A) → x ≡ y → (z : A) → y ≡ z → x ≡ z
  ≡trans-lem x .x refl = λ z r → r
  

-- the eliminator for Nat

Natelim : {ℓ : Level} → (C : Nat → Set ℓ) →
          C 0 → ((n : Nat) → C n → C (suc n)) → (n : Nat) → C n
Natelim C a b zero = a
Natelim C a b (suc n) = b n (Natelim C a b n)


-- Three

data ℕ₃ : Set where
  m₀ m₁ m₂ : ℕ₃

ℕ₃elim : {ℓ : Level} → (C : ℕ₃ → Set ℓ) →
         C m₀ → C m₁ → C m₂ → (x : ℕ₃) → C x
ℕ₃elim C a b c m₀ = a
ℕ₃elim C a b c m₁ = b
ℕ₃elim C a b c m₂ = c


-- disjoint sum

data _⊕_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  injl : A → A ⊕ B
  injr : B → A ⊕ B

⊕elim : {a b : Level} → {A : Set a} → {B : Set b} → (C : A ⊕ B → Set (a ⊔ b)) →
        ((c : A) → C (injl c)) → ((d : B) → C (injr d)) → (x : A ⊕ B) → C x
⊕elim C c d (injl x) = c x
⊕elim C c d (injr x) = d x

⊕elim' : {a b : Level} → {A : Set a} → {B : Set b} → (C : A ⊕ B → Set (lsuc (a ⊔ b))) →
        ((c : A) → C (injl c)) → ((d : B) → C (injr d)) → (x : A ⊕ B) → C x
⊕elim' C c d (injl x) = c x
⊕elim' C c d (injr x) = d x

infixl 20 _⊕_


-- pair types

_×_ : {a b : Level} → (A : Set a) → (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

infixl 20 _×_


-- finite ordinals
data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} → Fin n → Fin (suc n)

Finelim : {ℓ : Level} → (C : (n : Nat) → Fin n → Set ℓ) →
            ((n : Nat) → C (suc n) zero) → ((n : Nat) (i : Fin n) → C n i → C (suc n) (suc i)) →
              (n : Nat) (i : Fin n) → C n i
Finelim {ℓ} C base ind (suc n) zero = base n
Finelim {ℓ} C base ind (suc n) (suc i) = ind n i (Finelim C base ind n i)

cast : {n : Nat} → Fin n → Fin (suc n)
cast {.(suc _)} zero = zero
cast {.(suc _)} (suc i) = suc (cast i)


-- logical equivalence

_↔_ : {a b : Level} → (A : Set a) → (B : Set b) → Set (a ⊔ b)
A ↔ B = (A → B) × (B → A)

≡to↔ : {a : Level} {A B : Set a} → A ≡ B → A ↔ B
≡to↔ p = (λ x → transp (λ y → y) p x) , (λ x → transp (λ y → y) (≡sym p) x)


-- W-types (the type of well-founded trees)

data W {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  sup : (x : A) → (f : B x → W A B) → W A B

Welim : {a b : Level} → {A : Set a} → {B : A → Set b} → (C : W A B → Set (a ⊔ b)) →
        ((x : A) → (y : B x → W A B) → ((z : B x) → C (y z)) → C (sup x y)) →
        (c : W A B) → C c
Welim C f (sup x g) = f x g λ z → Welim C f (g z)

Welim' : {a b : Level} → {A : Set a} → {B : A → Set b} → (C : W A B → Set (lsuc (a ⊔ b))) →
        ((x : A) → (y : B x → W A B) → ((z : B x) → C (y z)) → C (sup x y)) →
        (c : W A B) → C c
Welim' C f (sup x g) = f x g λ z → Welim' C f (g z)

τ : {a b : Level} {A : Set a} {B : A → Set b} → W A B → Σ A (λ x → B x → W A B)
τ (sup x f) = x , f

-- the index of a tree

index : {a b : Level} {A : Set a} {B : A → Set b} → W A B → A
index a = fst (τ a)

-- the predecessors of a tree

pred : {a b : Level} {A : Set a} {B : A → Set b} → (a : W A B) → B (index a) → W A B
pred a = snd (τ a)

τ-comp : {a b : Level} {A : Set a} {B : A → Set b} → (a : W A B) → a ≡ sup (index a) (pred a)
τ-comp (sup x f) = refl


-- axiom of choice

AC : {a b : Level} → {A : Set a} → {B : Set b} → {C : A → B → Set (a ⊔ b)} →
       (∀ (x : A) → Σ B (λ y → C x y)) → Σ (A → B) (λ f → ∀ (x : A) → C x (f x))
AC prf = (λ x → fst (prf x)) , λ x → snd (prf x)
