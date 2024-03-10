{-# OPTIONS --without-K #-}

module LargeUniverses where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Nat
open import Preliminaries


-- Definition of Universes (𝕄 , 𝕊) and (ℚ , 𝔽 , 𝔾) of MLQ

{- 𝔸 consists of
   C : Set, F : C → (A : Set) → (B : A → Set) → Set, G : (x : C) → (A : Set) → (B : A → Set) → F x A B → Set,
   A : Set, B : A → Set -}
𝔸 : Set₁
𝔸 = Σ Set λ C → Σ (C → (A : Set) → (B : A → Set) → Set) λ F →
      Σ ((x : C) → (A : Set) → (B : A → Set) → F x A B → Set) λ _ → Σ Set λ A → A → Set

interleaved mutual

  data 𝕌 (D : 𝔸) : Set
  𝕋 : (D : 𝔸) → 𝕌 D → Set

  data 𝕌 (D : 𝔸) where
    ⋆ : 𝕌 D
    ◇ : 𝕌 D
    j : fst (snd (snd (snd D))) → 𝕌 D
    ♯ : fst D → (a : 𝕌 D) → (𝕋 D a → 𝕌 D) → 𝕌 D
    † : (e : fst D) → (a : 𝕌 D) → (b : 𝕋 D a → 𝕌 D) → fst (snd D) e (𝕋 D a) (λ x → 𝕋 D (b x)) → 𝕌 D
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

interleaved mutual

  data 𝕄 : Set
  𝕊 : 𝕄 → Set

  data ℚ : Set
  𝔽 : ℚ → (A : Set) → (B : A → Set) → Set
  𝔾 : (f : ℚ) → (A : Set) → (B : A → Set) → 𝔽 f A B → Set

  data 𝕄 where
    q : ℚ → (a : 𝕄) → (𝕊 a → 𝕄) → 𝕄
    ℓ : (f : ℚ) → (a : 𝕄) → (b : 𝕊 a → 𝕄) → 𝕊 (q f a b) → 𝕄

  𝕊 (q f a b) = 𝔽 f (𝕊 a) (λ y → 𝕊 (b y))
  𝕊 (ℓ f a b x) = 𝔾 f (𝕊 a) (λ y → 𝕊 (b y)) x

  data ℚ where
    u : (c : 𝕄) → (𝕊 c → ℚ) → ℚ

  𝔽 (u c f) A B = 𝕌 (𝕊 c , (λ x → 𝔽 (f x)) , (λ x → 𝔾 (f x)) , A , B)

  𝔾 (u c f) A B y = 𝕋 (𝕊 c , (λ x → 𝔽 (f x)) , (λ x → 𝔾 (f x)) , A , B) y


-- Definition of Higher-Order Universe Operators of ML(n)

-- Op n is the type of operators of order n
-- FamOp n is the type of families of operators in Op n
interleaved mutual

  Op : ℕ → Set₁
  FamOp : ℕ → Set₁

  Op zero = Set
  Op (suc n) = FamOp n → FamOp n

  FamOp n = Σ Set (λ A → A → Op n)

interleaved mutual

  ≤suc : {m n : ℕ} → m ≤ n → m ≤ suc n
  suc≤ : {m n : ℕ} → suc m ≤ n → m ≤ n

  ≤suc {zero} {n} x = z≤n
  ≤suc {suc m} {n} x = s≤s (suc≤ x)

  suc≤ {m} {.(suc _)} (s≤s x) = ≤suc x

{- our formulation of the system ML(n + 1) of higher-order universe operators has a family of types
   (𝕌h n A B m x, 𝕋h n A B m x) for any m ≤ n with a proof x of m ≤ n

   𝕌h n A B m x is a universe of universe operators of order m, and
   𝕋h n A B m x is its decoding function -}
interleaved mutual

  data 𝕌h (n : ℕ) (A : (m : ℕ) → m ≤ n → Set)
            (B : (m : ℕ) → (x : m ≤ n) → A m x → Op m) : (m : ℕ) → m ≤ n → Set
  𝕋h : (n : ℕ) → (A : (m : ℕ) → m ≤ n → Set) →
         (B : (m : ℕ) → (x : m ≤ n) → A m x → Op m) → (m : ℕ) → (x : m ≤ n) → 𝕌h n A B m x → Op m

  data 𝕌h (n : ℕ) (A : (m : ℕ) → m ≤ n → Set) (B : (m : ℕ) → (x : m ≤ n) → A m x → Op m) where
    ∗ : (m : ℕ) → m ≤ n → 𝕌h n A B 0 z≤n
    ℓ : (m : ℕ) → (x : m ≤ n) → A m x → 𝕌h n A B m x
    𝕦 : (m : ℕ) → (x : suc m ≤ n) → (o : 𝕌h n A B (suc m) x) → (a : 𝕌h n A B 0 z≤n) →
          (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B m (suc≤ x)) → 𝕌h n A B zero z≤n
    𝕥 : (m : ℕ) → (x : suc m ≤ n) → (o : 𝕌h n A B (suc m) x) → (a : 𝕌h n A B 0 z≤n) →
          (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B m (suc≤ x)) → 𝕋h n A B 0 z≤n (𝕦 m x o a b) → 𝕌h n A B m (suc≤ x)
    code⊥ : 𝕌h n A B 0 z≤n
    code⊤ : 𝕌h n A B 0 z≤n
    codeB : 𝕌h n A B 0 z≤n
    codeN : 𝕌h n A B 0 z≤n
    codeS : 𝕌h n A B 0 z≤n → 𝕌h n A B 0 z≤n → 𝕌h n A B 0 z≤n
    codeE : (x : 𝕌h n A B 0 z≤n) → (a b : 𝕋h n A B 0 z≤n x) → 𝕌h n A B 0 z≤n
    codeΠ : (a : 𝕌h n A B 0 z≤n) → (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B 0 z≤n) → 𝕌h n A B 0 z≤n
    codeΣ : (a : 𝕌h n A B 0 z≤n) → (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B 0 z≤n) → 𝕌h n A B 0 z≤n
    codeW : (a : 𝕌h n A B 0 z≤n) → (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B 0 z≤n) → 𝕌h n A B 0 z≤n

  𝕋h n A B .0 .z≤n (∗ m x) = A m x
  𝕋h n A B m x (ℓ .m .x y) = B m x y
  𝕋h n A B .0 .z≤n (𝕦 m x o a b) =
    fst (𝕋h n A B (suc m) x o (𝕋h n A B 0 z≤n a , λ y → 𝕋h n A B m (suc≤ x) (b y)))
  𝕋h n A B m .(suc≤ x) (𝕥 .m x o a b y) =
    snd (𝕋h n A B (suc m) x o (𝕋h n A B 0 z≤n a , λ z → 𝕋h n A B m (suc≤ x) (b z))) y
  𝕋h n A B 0 z≤n code⊥ = ⊥
  𝕋h n A B 0 z≤n code⊤ = ⊤
  𝕋h n A B 0 z≤n codeB = Bool
  𝕋h n A B 0 z≤n codeN = ℕ
  𝕋h n A B 0 z≤n (codeS a b) = (𝕋h n A B 0 z≤n a) ⊕ (𝕋h n A B 0 z≤n b)
  𝕋h n A B 0 z≤n (codeE x a b) = a ≡ b
  𝕋h n A B 0 z≤n (codeΠ a b) = (x : 𝕋h n A B 0 z≤n a) → 𝕋h n A B 0 z≤n (b x)
  𝕋h n A B 0 z≤n (codeΣ a b) = Σ (𝕋h n A B 0 z≤n a) (λ x → 𝕋h n A B 0 z≤n (b x))
  𝕋h n A B 0 z≤n (codeW a b) = W (𝕋h n A B 0 z≤n a) (λ x → 𝕋h n A B 0 z≤n (b x))


-- external Mahlo universe

{- the sort Set is considered as an external Mahlo universe

   for any function f on Σ Set (λ A → A → Set),
   a subuniverse closed under f is defined as (𝕌m , 𝕋m) -}
interleaved mutual

  data 𝕌m (f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)) : Set
  𝕋m : (f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)) → 𝕌m f → Set

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

-- injection function

ι : {f : Σ Set (λ A → A → Set) → Σ Set (λ A → A → Set)} →
    Σ (𝕌m f) (λ x → 𝕋m f x → 𝕌m f) → Σ Set (λ A → A → Set)
ι {f} (c₁ , c₂) = 𝕋m f c₁ , λ x → 𝕋m f (c₂ x)


-- higher-order Mahlo universe operators

{- for any m with m ≤ n and any function f on Σ Set (λ A → A → Op m) → Σ Set (λ A → A → Op m),
   i.e., families of operators of order m,
   
   we define a universe (𝕌hm n f m x , 𝕋hm n f m x) closed under f, where x is a proof of m ≤ n

   the case of m = 0 corresponds to the external Mahlo universe -}
interleaved mutual

  data 𝕌hm (n : ℕ) (f : (m : ℕ) → m ≤ n → Σ Set (λ A → A → Op m) → Σ Set (λ A → A → Op m)) : (m : ℕ) → m ≤ n → Set
  𝕋hm : (n : ℕ) → (f : (m : ℕ) → m ≤ n → Σ Set (λ A → A → Op m) → Σ Set (λ A → A → Op m)) →
          (m : ℕ) → (x : m ≤ n) → 𝕌hm n f m x → Op m

  data 𝕌hm n f where
    code₁ : (m : ℕ) → (x : m ≤ n) → Σ (𝕌hm n f 0 z≤n) (λ a → 𝕋hm n f 0 z≤n a → 𝕌hm n f m x) → 𝕌hm n f 0 z≤n
    code₂ : (m : ℕ) → (x : m ≤ n) → (c : Σ (𝕌hm n f 0 z≤n) (λ a → 𝕋hm n f 0 z≤n a → 𝕌hm n f m x)) →
      𝕋hm n f 0 z≤n (code₁ m x c) → 𝕌hm n f m x
    code⊥ : 𝕌hm n f 0 z≤n
    code⊤ : 𝕌hm n f 0 z≤n
    codeB : 𝕌hm n f 0 z≤n
    codeN : 𝕌hm n f 0 z≤n
    codeS : 𝕌hm n f 0 z≤n → 𝕌hm n f 0 z≤n → 𝕌hm n f 0 z≤n
    codeE : (x : 𝕌hm n f 0 z≤n) → (a b : 𝕋hm n f 0 z≤n x) → 𝕌hm n f 0 z≤n
    codeΠ : (a : 𝕌hm n f 0 z≤n) → (b : 𝕋hm n f 0 z≤n a → 𝕌hm n f 0 z≤n) → 𝕌hm n f 0 z≤n
    codeΣ : (a : 𝕌hm n f 0 z≤n) → (b : 𝕋hm n f 0 z≤n a → 𝕌hm n f 0 z≤n) → 𝕌hm n f 0 z≤n
    codeW : (a : 𝕌hm n f 0 z≤n) → (b : 𝕋hm n f 0 z≤n a → 𝕌hm n f 0 z≤n) → 𝕌hm n f 0 z≤n

  𝕋hm n f .0 .z≤n (code₁ m x c) = fst (f m x (𝕋hm n f 0 z≤n (fst c) , λ y → 𝕋hm n f m x (snd c y)))
  𝕋hm n f m x (code₂ .m .x c y) = snd (f m x (𝕋hm n f 0 z≤n (fst c) , λ z → 𝕋hm n f m x (snd c z))) y
  𝕋hm n f 0 z≤n code⊥ = ⊥
  𝕋hm n f 0 z≤n code⊤ = ⊤
  𝕋hm n f 0 z≤n codeB = Bool
  𝕋hm n f 0 z≤n codeN = ℕ
  𝕋hm n f 0 z≤n (codeS a b) = (𝕋hm n f 0 z≤n a) ⊕ (𝕋hm n f 0 z≤n b)
  𝕋hm n f 0 z≤n (codeE x a b) = a ≡ b
  𝕋hm n f 0 z≤n (codeΠ a b) = (x : 𝕋hm n f 0 z≤n a) → 𝕋hm n f 0 z≤n (b x)
  𝕋hm n f 0 z≤n (codeΣ a b) = Σ (𝕋hm n f 0 z≤n a) (λ x → 𝕋hm n f 0 z≤n (b x))
  𝕋hm n f 0 z≤n (codeW a b) = W (𝕋hm n f 0 z≤n a) (λ x → 𝕋hm n f 0 z≤n (b x))
