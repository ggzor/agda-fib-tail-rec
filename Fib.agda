open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

-- Fibonacci canónico
fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- Fibonacci tail-rec
itero : (n : ℕ) → ℕ → ℕ → 2 ≤ n → ℕ
itero 0 i j ()
itero 1 i j (s≤s ())
itero 2 i j _ = i + j
itero (suc n-1@(suc (suc n))) i j _ = itero n-1 j (i + j) (s≤s (s≤s z≤n))

-- Un lema adicional
∸-suc : ∀ (n k : ℕ) → k ≤ n → suc n ∸ k ≡ suc (n ∸ k)
∸-suc n zero z≤n = refl
∸-suc (suc n) (suc k) (s≤s k≤n) = ∸-suc n k k≤n

-- Proposición 2.1
prop-2-1 : ∀ (n k : ℕ)
         → (p : k ≤ n)
         →   itero (suc (suc n)) 0 1                         (s≤s (s≤s z≤n))
           ≡ itero (suc (suc (n ∸ k))) (fib k) (fib (suc k)) (s≤s (s≤s z≤n))
prop-2-1 n zero p = refl
prop-2-1 (suc n) (suc k) (s≤s p) with prop-2-1 (suc n) k (≤-step p)
... | h-ind rewrite ∸-suc n k p = h-ind

-- Al final se prueba que itero calcula lo mismo que el
-- fibonacci canónico para todo n≥2.
same-fib : ∀ (n : ℕ)
         → (p : 2 ≤ n)
         → itero n 0 1 p ≡ fib n
same-fib 0 ()
same-fib 1 (s≤s ())
same-fib (suc (suc n)) (s≤s (s≤s z≤n)) with prop-2-1 n n ≤-refl
... | prop-n-2 rewrite n∸n≡0 n = prop-n-2

