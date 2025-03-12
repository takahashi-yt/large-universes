{-# OPTIONS --without-K #-}

module HOUOperator where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Data.Nat
open import Preliminaries


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
