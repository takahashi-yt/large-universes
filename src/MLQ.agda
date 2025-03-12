{-# OPTIONS --cubical-compatible #-}

module MLQ where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Nat
open import Preliminaries


-- Definition of the two universes (𝕄 , 𝕊) and (ℚ , 𝔽 , 𝔾) of MLQ

-- We first define a universe (𝕌 D , 𝕋 D)

-- 𝔸 below is the type of tuples which consist of
-- C : Set,
-- F : C → (A : Set) → (B : A → Set) → Set,
-- G : (x : C) → (A : Set) → (B : A → Set) → F x A B → Set,
-- A : Set,
-- B : A → Set
--
-- Elements of C are indices, and (F , G) can be considered as
-- a C-indexed family of operators of type (Σ Set λ A → Set) → (Σ Set λ A → Set)
-- That is, an operator f in F takes (X , Y) : Σ Set λ A → Set, and returns a set
--
-- The corresponding operator g in G takes (X , Y), and returns a family of sets
-- indexed by the set given by f (X , Y)
--
-- (A , B) is a usual family of Sets

𝔸 : Set₁
𝔸 = Σ Set λ C → Σ (C → (A : Set) → (B : A → Set) → Set) λ F →
      Σ ((x : C) → (A : Set) → (B : A → Set) → F x A B → Set) λ _ → Σ Set λ A → A → Set

-- For a given D = (C , F , G , A , B) : 𝔸, we define the universe (𝕌 D , 𝕋 D) such that
-- it contains C , A , B a for each a : A
-- Moreover, (𝕌 D , 𝕋 D) is closed under all operators in (F , G)

interleaved mutual

  data 𝕌 (D : 𝔸) : Set
  𝕋 : (D : 𝔸) → 𝕌 D → Set

  data 𝕌 (D : 𝔸) where  -- let D be (C , F , G , A , B)
    ⋆ : 𝕌 D  -- the code of C
    ◇ : 𝕌 D  -- the code of A
    j : fst (snd (snd (snd D))) → 𝕌 D  -- the code of B
    ♯ : fst D → (a : 𝕌 D) → (𝕋 D a → 𝕌 D) → 𝕌 D  -- the code of F
    † : (e : fst D) → (a : 𝕌 D) → (b : 𝕋 D a → 𝕌 D) →  -- the code of G
          fst (snd D) e (𝕋 D a) (λ x → 𝕋 D (b x)) → 𝕌 D
    code⊥ : 𝕌 D
    code⊤ : 𝕌 D
    codeB : 𝕌 D
    codeN : 𝕌 D
    codeS : 𝕌 D → 𝕌 D → 𝕌 D
    codeE : (x : 𝕌 D) → (a b : 𝕋 D x) → 𝕌 D
    codeΠ : (a : 𝕌 D) → (b : 𝕋 D a → 𝕌 D) → 𝕌 D
    codeΣ : (a : 𝕌 D) → (b : 𝕋 D a → 𝕌 D) → 𝕌 D
    codeW : (a : 𝕌 D) → (b : 𝕋 D a → 𝕌 D) → 𝕌 D

  𝕋 D ⋆ = fst D
  𝕋 D ◇ = fst (snd (snd (snd D)))
  𝕋 D (j a) = snd (snd (snd (snd D))) a
  𝕋 D (♯ e a b) = fst (snd D) e (𝕋 D a) (λ x → 𝕋 D (b x))
  𝕋 D († e a b x) = fst (snd (snd D)) e (𝕋 D a) (λ x → 𝕋 D (b x)) x
  𝕋 D code⊥ = ⊥
  𝕋 D code⊤ = ⊤
  𝕋 D codeB = Bool
  𝕋 D codeN = ℕ
  𝕋 D (codeS a b) = (𝕋 D a) ⊕ (𝕋 D b)
  𝕋 D (codeE x a b) = a ≡ b
  𝕋 D (codeΠ a b) = (x : 𝕋 D a) → 𝕋 D (b x)
  𝕋 D (codeΣ a b) = Σ (𝕋 D a) (λ x → 𝕋 D (b x))
  𝕋 D (codeW a b) = W (𝕋 D a) (λ x → 𝕋 D (b x))

-- (ℚ , 𝔽 , 𝔾) is the universe such that
-- elements of ℚ are codes of universe operators:
-- the constructor u of ℚ takes a family of (codes of) universe operators as an input,
-- and returns a (code of) universe operator giving a universe being closed under all operators in this family
--
-- 𝔽 and 𝔾 are the decoding functions for ℚ
--
-- (𝕄 , 𝕊) is the universe closed under all operators in ℚ
--
-- (𝕄 , 𝕊) and (ℚ , 𝔽 , 𝔾) are defined by simultaneous induction-recursion
--
-- The universe (𝕌 D , 𝕋 D) above is used in the definition of (ℚ , 𝔽 , 𝔾)

interleaved mutual

  data 𝕄 : Set
  𝕊 : 𝕄 → Set

  data ℚ : Set
  𝔽 : ℚ → (A : Set) → (B : A → Set) → Set
  𝔾 : (f : ℚ) → (A : Set) → (B : A → Set) → 𝔽 f A B → Set

  data 𝕄 where
    q : ℚ → (a : 𝕄) → (𝕊 a → 𝕄) → 𝕄
    ℓ : (f : ℚ) → (a : 𝕄) → (b : 𝕊 a → 𝕄) → 𝕊 (q f a b) → 𝕄
    code⊥ : 𝕄
    code⊤ : 𝕄
    codeB : 𝕄
    codeN : 𝕄
    codeS : 𝕄 → 𝕄 → 𝕄
    codeE : (x : 𝕄) → (a b : 𝕊 x) → 𝕄
    codeΠ : (a : 𝕄) → (b : 𝕊 a → 𝕄) → 𝕄
    codeΣ : (a : 𝕄) → (b : 𝕊 a → 𝕄) → 𝕄
    codeW : (a : 𝕄) → (b : 𝕊 a → 𝕄) → 𝕄

  𝕊 (q f a b) = 𝔽 f (𝕊 a) (λ y → 𝕊 (b y))
  𝕊 (ℓ f a b x) = 𝔾 f (𝕊 a) (λ y → 𝕊 (b y)) x
  𝕊 code⊥ = ⊥
  𝕊 code⊤ = ⊤
  𝕊 codeB = Bool
  𝕊 codeN = ℕ
  𝕊 (codeS a b) = (𝕊 a) ⊕ (𝕊 b)
  𝕊 (codeE x a b) = a ≡ b
  𝕊 (codeΠ a b) = (x : 𝕊 a) → 𝕊 (b x)
  𝕊 (codeΣ a b) = Σ (𝕊 a) (λ x → 𝕊 (b x))
  𝕊 (codeW a b) = W (𝕊 a) (λ x → 𝕊 (b x))

  data ℚ where
    u : (c : 𝕄) → (𝕊 c → ℚ) → ℚ

  𝔽 (u c f) A B = 𝕌 (𝕊 c , (λ x → 𝔽 (f x)) , (λ x → 𝔾 (f x)) , A , B)

  𝔾 (u c f) A B y = 𝕋 (𝕊 c , (λ x → 𝔽 (f x)) , (λ x → 𝔾 (f x)) , A , B) y
