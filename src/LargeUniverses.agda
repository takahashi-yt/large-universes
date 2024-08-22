{-# OPTIONS --without-K #-}

module LargeUniverses where

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


-- Definition of Higher-Order Universe Operators of ML(n)

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

-- Useful lemmas for the natural number indices

interleaved mutual

  ≤suc : {m n : ℕ} → m ≤ n → m ≤ suc n
  pred≤ : {m n : ℕ} → m ≤ n → Data.Nat.pred m ≤ n

  ≤suc {0} {n} x = z≤n
  ≤suc {suc m} {n} x = s≤s (pred≤ x)

  pred≤ {0} {n} x = x
  pred≤ {suc m} {0} ()
  pred≤ {suc m} {suc n} x = ≤suc (s≤s⁻¹ x)

-- 𝕌h is an ℕ-indexed family of universes of higher-order universe operators, and
-- 𝕋h is an ℕ-indexed family of the decoding functions
-- They are defined by indexed induction-recursion with the parameters A and B
--
-- Both 𝕌h n and 𝕋h n have two parameters A and B:
-- A is a family {A m, A (m - 1), ... , A 0} of Sets with m ≤ n, and
-- for each m with m ≤ n, B m is a family of operators of finite order such that
-- B m x is an operator of the m-th order for each x : A m
--
-- 𝕌h n A B 0 has codes of A m, A (m - 1), ... , A 0, and
-- 𝕌h n A B m has a code of B m x for each x : A m
--
-- Codes in 𝕌h n A B m are defined inductively from these basic codes by applying
-- a (code of) universe operator of (m + 1)-order in 𝕌h n A B (m + 1)
--
-- Note that we provide a proof x of m ≤ n to 𝕌 n A B m and 𝕋 n A B m as an index due to the condition m ≤ n
--
-- The system ML(n + 1) consists of
-- (𝕌 n A B n x , 𝕋 n A B n x), (𝕌 n A B (n - 1) x' , 𝕋 n A B (n - 1) x'), ... , (𝕌 n A B 0 x'' , 𝕋 n A B 0 x'')

interleaved mutual

  data 𝕌h (n : ℕ) (A : (m : ℕ) → m ≤ n → Set)
            (B : (m : ℕ) → (x : m ≤ n) → A m x → Op m) : (m : ℕ) → m ≤ n → Set
  𝕋h : (n : ℕ) → (A : (m : ℕ) → m ≤ n → Set) →
         (B : (m : ℕ) → (x : m ≤ n) → A m x → Op m) → (m : ℕ) → (x : m ≤ n) → 𝕌h n A B m x → Op m

  -- (𝕦 , 𝕥) takes a (code of) family of universe operators of m-th order and
  -- returns a (code of) new family of m-th order universe operators obtained by
  -- applying an (m + 1)-th universe operator
  
  data 𝕌h (n : ℕ) (A : (m : ℕ) → m ≤ n → Set) (B : (m : ℕ) → (x : m ≤ n) → A m x → Op m) where
    ∗ : (m : ℕ) → m ≤ n → 𝕌h n A B 0 z≤n  -- the codes of A m for each m
    ℓ : (m : ℕ) → (x : m ≤ n) → 𝕋h n A B 0 z≤n (∗ m x) → 𝕌h n A B m x  -- the codes of B m for each m
    𝕦 : (m : ℕ) → (x : suc m ≤ n) → (o : 𝕌h n A B (suc m) x) → (a : 𝕌h n A B 0 z≤n) →
          (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B m (pred≤ x)) → 𝕌h n A B 0 z≤n
    𝕥 : (m : ℕ) → (x : suc m ≤ n) → (o : 𝕌h n A B (suc m) x) → (a : 𝕌h n A B 0 z≤n) →
          (b : 𝕋h n A B 0 z≤n a → 𝕌h n A B m (pred≤ x)) → 𝕋h n A B 0 z≤n (𝕦 m x o a b) → 𝕌h n A B m (pred≤ x)
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
    fst (𝕋h n A B (suc m) x o (𝕋h n A B 0 z≤n a , λ y → 𝕋h n A B m (pred≤ x) (b y)))
  𝕋h n A B m .(pred≤ x) (𝕥 .m x o a b y) =
    snd (𝕋h n A B (suc m) x o (𝕋h n A B 0 z≤n a , λ z → 𝕋h n A B m (pred≤ x) (b z))) y
  𝕋h n A B 0 z≤n code⊥ = ⊥
  𝕋h n A B 0 z≤n code⊤ = ⊤
  𝕋h n A B 0 z≤n codeB = Bool
  𝕋h n A B 0 z≤n codeN = ℕ
  𝕋h n A B 0 z≤n (codeS a b) = (𝕋h n A B 0 z≤n a) ⊕ (𝕋h n A B 0 z≤n b)
  𝕋h n A B 0 z≤n (codeE x a b) = a ≡ b
  𝕋h n A B 0 z≤n (codeΠ a b) = (x : 𝕋h n A B 0 z≤n a) → 𝕋h n A B 0 z≤n (b x)
  𝕋h n A B 0 z≤n (codeΣ a b) = Σ (𝕋h n A B 0 z≤n a) (λ x → 𝕋h n A B 0 z≤n (b x))
  𝕋h n A B 0 z≤n (codeW a b) = W (𝕋h n A B 0 z≤n a) (λ x → 𝕋h n A B 0 z≤n (b x))


-- MLQ as an instance of ML(3)

1≤1 : 1 ≤ 1
1≤1 = s≤s z≤n

2≤2 : 2 ≤ 2
2≤2 = s≤s 1≤1

1≤2 : 1 ≤ 2
1≤2 = s≤s z≤n

Q₁ : Op 1
Q₁ (A , B) =  𝕌h 0 A' B' 0 z≤n , 𝕋h 0 A' B' 0 z≤n
  where
  A' : (m : ℕ) → m ≤ 0 → Set
  A' m x = A

  B' : (m : ℕ) → (x : m ≤ 0) → A' m x → Op m
  B' 0 x y = B y

Q₂ : FamOp 1 → Op 1
Q₂ (I , J) (A , B) = 𝕌h 1 A' B' 0 z≤n , 𝕋h 1 A' B' 0 z≤n 
  where
  A' : (m : ℕ) → m ≤ 1 → Set
  A' 0 x = A
  A' (suc m) x = I

  B' : (m : ℕ) → (x : m ≤ 1) → A' m x → Op m
  B' 0 x y = B y
  B' 1 (s≤s x) y = J y

Q̄₂ : Op 2
Q̄₂ (I , J) = ⊤ , λ _ → Q₂ (I , J)

postulate
  X : Set
  Y : X → Set
  
A' : (m : ℕ) → m ≤ 2 → Set
A' 0 x = X
A' (suc m) x = ⊤

B' : (m : ℕ) → (x : m ≤ 2) → A' m x → Op m
B' 0 x = Y
B' (suc 0) (s≤s x) = λ _ → Q₁
B' (suc (suc 0)) (s≤s (s≤s x)) = λ _ → Q̄₂

𝕄' : Set
𝕄' = 𝕌h 2 A' B' 0 z≤n

𝕊' : 𝕌h 2 A' B' 0 z≤n → Set
𝕊' = 𝕋h 2 A' B' 0 z≤n

ℚ' : Set
ℚ' = 𝕌h 2 A' B' 1 1≤2

𝔽' : ℚ' → (A : Set) → (B : A → Set) → Set
𝔽' f A B = fst (𝕋h 2 A' B' 1 1≤2 f (A , B))

𝔾' : (f : ℚ') → (A : Set) → (B : A → Set) → 𝔽' f A B → Set
𝔾' f A B x = snd (𝕋h 2 A' B' 1 1≤2 f (A , B)) x


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
