module Pigeonhole where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

caseAnalysis : ∀ n x → (f : ℕ → ℕ)
              → (∃[ m ] (m < n × f m ≡ x)) ⊎ (∄[ m ] (m < n × f m ≡ x))
caseAnalysis 0 x f = inj₂ (λ {(_ , () , _)})
caseAnalysis (suc n) x f with caseAnalysis n x f
caseAnalysis (suc n) x f  | inj₁ (m , m<n , fm≡x) = inj₁ (m , ≤-trans m<n (n≤1+n n) , fm≡x)
caseAnalysis (suc n) x f  | inj₂ ¬exists with f n ≟ x
... | yes fn≡x = inj₁ (n , ≤-refl , fn≡x)
... | no ¬fn≡x = inj₂ lem
  where
    lem : ∄[ m ] (m < suc n × f m ≡ x)
    lem (m , m<n+1 , fm≡x) with m≤n⇒m<n∨m≡n m<n+1
    ... | inj₁ (s≤s m<n) = ¬exists (m , m<n , fm≡x)
    ... | inj₂ refl = ¬fn≡x fm≡x

pigeonhole : ∀ N → (f : ℕ → ℕ)
           → (∀ n → n ≤ N → f n < N)
           → ∃[ m ] ∃[ n ] (m < n × n ≤ N × f n ≡ f m)
pigeonhole 0 f prop with prop 0 z≤n
... | ()
pigeonhole (suc N) f prop with caseAnalysis (suc N) (f (suc N)) f
... | inj₁ (m , m≤n , fm≡fN+1) = m , suc N , m≤n , ≤-refl , sym fm≡fN+1
... | inj₂ ¬exists = thm
  where
  g : ℕ → ℕ
  g x with (f x) ≟ N
  ... | yes refl = f (suc N)
  ... | no  _ = f x

  prop' : ∀ x → x ≤ N → g x < N
  prop' x x≤N with (f x) ≟ N
  ... | yes refl = ≤∧≢⇒< lem₂ lem₁
    where
    lem₁ : f (suc N) ≢ N
    lem₁ fx≡fN+1 = ¬exists (x , s≤s x≤N , sym fx≡fN+1)

    lem₂ : f (suc N) ≤ N
    lem₂ with prop (suc N) ≤-refl
    ... | s≤s fN+1≤N = fN+1≤N
  ... | no  fx≢N = ≤∧≢⇒< (+-cancelˡ-≤ 1 (prop x (≤-trans x≤N (n≤1+n N)))) fx≢N

  thm : ∃[ m ] ∃[ n ] (m < n × n ≤ suc N × f n ≡ f m)
  thm with pigeonhole N g prop'
  ... | (m , n , m<n , n<N+1 , gn≡gm) = m , n , m<n , ≤-trans n<N+1 (n≤1+n N) , lem₁
    where
    lem₁ : f n ≡ f m
    lem₁ with (f m) ≟ N
    lem₁ | (yes fm≡N) with (f n) ≟ N
    lem₁ | (yes fm≡N) | (yes fn≡N) = trans fn≡N (sym fm≡N)
    lem₁ | (yes refl) | (no fn≠N) = ⊥-elim (¬exists (n , s≤s n<N+1 , gn≡gm))
    lem₁ | (no  fm≠N) with (f n) ≟ N
    lem₁ | (no  fm≠N) | (yes refl) = ⊥-elim (¬exists (m , ≤-trans m<n (≤-trans n<N+1 (n≤1+n N)) , sym gn≡gm))
    lem₁ | (no  fm≠N) | (no fn≠N) = gn≡gm
