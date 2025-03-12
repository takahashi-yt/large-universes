{-# OPTIONS --cubical-compatible #-}

module MahloHOSubuniverse where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Nat
open import Preliminaries


-- Op n is the type of operators of order n,
-- where an operator of 0-order is defined as a Set
-- FamOp n is the type of families of operators in Op n,
-- so FamOp 0 is a family of Sets

interleaved mutual

  Op : ℕ → Set₁
  FamOp : ℕ → Set₁

  Op 0 = Set
  Op (suc n) = FamOp n → FamOp n

  FamOp n = Σ Set (λ A → A → Op n)


-- Definition of external Mahlo universe

-- The sort Set is considered as an external Mahlo universe
--
-- For any function f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set), i.e., f : Op 1,
-- a subuniverse closed under f is defined as (𝕌m f , 𝕋m f) by induction-recursion with the parameter f

interleaved mutual

  data 𝕌m (f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)) : Set
  𝕋m : (f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)) → 𝕌m f → Set

  -- code₁ and code₂ represent the restriction of f to 𝕌m f
  
  data 𝕌m f where
    code₁ : Σ (𝕌m f) (λ a → 𝕋m f a → 𝕌m f) → 𝕌m f
    code₂ : (c : Σ (𝕌m f) (λ a → 𝕋m f a → 𝕌m f)) → 𝕋m f (code₁ c) → 𝕌m f
    code⊥ : 𝕌m f
    code⊤ : 𝕌m f
    codeB : 𝕌m f
    codeN : 𝕌m f
    codeS : 𝕌m f → 𝕌m f → 𝕌m f
    codeE : (x : 𝕌m f) → (a b : 𝕋m f x) → 𝕌m f
    codeΠ : (a : 𝕌m f) → (b : 𝕋m f a → 𝕌m f) → 𝕌m f
    codeΣ : (a : 𝕌m f) → (b : 𝕋m f a → 𝕌m f) → 𝕌m f
    codeW : (a : 𝕌m f) → (b : 𝕋m f a → 𝕌m f) → 𝕌m f

  𝕋m f (code₁ c) = fst (f (𝕋m f (fst c) , λ x → 𝕋m f (snd c x)))
  𝕋m f (code₂ c d) = snd (f (𝕋m f (fst c) , λ x → 𝕋m f (snd c x))) d
  𝕋m f code⊥ = ⊥
  𝕋m f code⊤ = ⊤
  𝕋m f codeB = Bool
  𝕋m f codeN = ℕ
  𝕋m f (codeS a b) = (𝕋m f a) ⊕ (𝕋m f b)
  𝕋m f (codeE x a b) = a ≡ b
  𝕋m f (codeΠ a b) = (x : 𝕋m f a) → 𝕋m f (b x)
  𝕋m f (codeΣ a b) = Σ (𝕋m f a) (λ x → 𝕋m f (b x))
  𝕋m f (codeW a b) = W (𝕋m f a) (λ x → 𝕋m f (b x))

-- the injection function

ι : {f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)} →
    Σ (𝕌m f) (λ x → 𝕋m f x → 𝕌m f) → Σ Set (λ A → A → Set)
ι {f} (c₁ , c₂) = 𝕋m f c₁ , λ x → 𝕋m f (c₂ x)


-- Definition of the external Mahlo universe with higher-order subuniverses
-- Note that this extended Mahlo universe coincides with the union ⋃ { ML(n) ∣ n : ℕ }
--
-- Higher-order subuniverses are defined by indexed induction-recursion with the parameters A and B
-- Similar to the case of universes of higher-order universe operators,
-- A is an ℕ-indexed family of Sets, and 
-- for each n : ℕ, B n is a family of operators such that
-- B n x is an operator of n-th order for each x : A n, where a 0-th operator is nothing but a Set
-- The parameter f in the subuniverse 𝕌m f of the external Mahlo universe is a special case of (A 1 , B 1),
-- that is, A 1 = ⊤ and B 1 = λ x → f
--
-- Since the subuniverse 𝕌mh A B m has a code for each operator in B m (see the constructor ℓ below),
-- the closedness of 𝕌mh A B n under all operators in B (n + 1) is shown by the constructors 𝕦 and 𝕥:
-- take an argument o for 𝕦 and 𝕥 as the code of an operator in B (n + 1)
--
-- Compared with the external Mahlo universe above, the strength of its variant with higher-order subuniverses
-- consists in the fact that the subuniverse 𝕌mh A B 0 is closed not only under
-- the first-order operators in (A 1 , B 1), but also under all first-order operators obtained by
-- applying A, B, ∗, ℓ, 𝕦, 𝕥 in this system

interleaved mutual

  data 𝕌mh (A : ℕ → Set) (B : (n : ℕ) → A n → Op n) : ℕ → Set
  𝕋mh : (A : ℕ → Set) (B : (n : ℕ) → A n → Op n) → (n : ℕ) → 𝕌mh A B n → Op n

  data 𝕌mh A B where
    * : ℕ → 𝕌mh A B 0
    ℓ : (n : ℕ) → 𝕋mh A B 0 (* n) → 𝕌mh A B n
    𝕦 : (n : ℕ) → (o : 𝕌mh A B (suc n)) → Σ (𝕌mh A B 0) (λ a → 𝕋mh A B 0 a → 𝕌mh A B n) → 𝕌mh A B 0
    𝕥 : (n : ℕ) → (o : 𝕌mh A B (suc n)) → (c : Σ (𝕌mh A B 0) (λ a → 𝕋mh A B 0 a → 𝕌mh A B n)) →
              𝕋mh A B 0 (𝕦 n o c) → 𝕌mh A B n
    code⊥ : 𝕌mh A B 0
    code⊤ : 𝕌mh A B 0
    codeB : 𝕌mh A B 0
    codeN : 𝕌mh A B 0
    codeS : 𝕌mh A B 0 → 𝕌mh A B 0 → 𝕌mh A B 0
    codeE : (x : 𝕌mh A B 0) → (a b : 𝕋mh A B 0 x) → 𝕌mh A B 0
    codeΠ : (a : 𝕌mh A B 0) → (b : 𝕋mh A B 0 a → 𝕌mh A B 0) → 𝕌mh A B 0
    codeΣ : (a : 𝕌mh A B 0) → (b : 𝕋mh A B 0 a → 𝕌mh A B 0) → 𝕌mh A B 0
    codeW : (a : 𝕌mh A B 0) → (b : 𝕋mh A B 0 a → 𝕌mh A B 0) → 𝕌mh A B 0

  𝕋mh A B .0 (* n) = A n
  𝕋mh A B n (ℓ n x) = B n x
  𝕋mh A B .0 (𝕦 n o c) = fst (𝕋mh A B (suc n) o (𝕋mh A B 0 (fst c) , λ y → 𝕋mh A B n (snd c y)))
  𝕋mh A B n (𝕥 .n o c x) = snd (𝕋mh A B (suc n) o (𝕋mh A B 0 (fst c) , λ y → 𝕋mh A B n (snd c y))) x
  𝕋mh A B .0 code⊥ = ⊥
  𝕋mh A B .0 code⊤ = ⊤
  𝕋mh A B .0 codeB = Bool
  𝕋mh A B .0 codeN = ℕ
  𝕋mh A B .0 (codeS a b) = (𝕋mh A B 0 a) ⊕ (𝕋mh A B 0 b)
  𝕋mh A B .0 (codeE a x y) = x ≡ y
  𝕋mh A B .0 (codeΠ a b) = (x : 𝕋mh A B 0 a) → 𝕋mh A B 0 (b x)
  𝕋mh A B .0 (codeΣ a b) = Σ (𝕋mh A B 0 a) λ x → 𝕋mh A B 0 (b x)
  𝕋mh A B .0 (codeW a b) = W (𝕋mh A B 0 a) λ x → 𝕋mh A B 0 (b x)
