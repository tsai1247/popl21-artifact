import Level as L
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂ ; cong-app; subst)
open import Data.Product
open import Data.Empty
open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat
open import Data.Nat.Properties using ( +-suc ; +-comm ; +-assoc ; <-trans ; ≤-trans ; +-identityʳ ; <⇒≤)
open import RevMachine

open import Function.Bijection using ( _⤖_ ; Bijection )
open import Data.Fin using ( Fin ; toℕ ; fromℕ<)
open import Relation.Nullary

open import Pigeonhole

module BroadRevTermination {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine.RevMachine M
  open import RevNoRepeat M

----------------------
  -- 把 State ⤖ Fin N 中的 to 跟 from 拉出來用
  to : ∀ {N st₀} → (∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N ) → ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) → Fin N
  to record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = bijective } ∃stₘ[] = _⟨$⟩_ ∃stₘ[]

  from : ∀ {N st₀} → (∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N ) → Fin N → ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ)
  from record { to = to ; bijective = record { injective = injective ; surjective = record { from = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; right-inverse-of = right-inverse-of } } } fn = _⟨$⟩_ fn

  to-from : ∀ {N st₀}
    → (St-Fin :  ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → (∃stₘ[] : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ))
    → from St-Fin (to St-Fin ∃stₘ[]) ≡ ∃stₘ[]
  to-from record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = record { injective = injective ; surjective = record { from = from ; right-inverse-of = right-inverse-of } } } ∃stₘ[] = injective (right-inverse-of (_⟨$⟩_ ∃stₘ[]))

  from-to : ∀ {N st₀}
    → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → (fn : Fin N)
    → to St-Fin (from St-Fin fn) ≡ fn
  from-to record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = record { injective = injective ; surjective = record { from = from ; right-inverse-of = right-inverse-of } } } st = right-inverse-of st
-----------------------------------------

  private
    split↦ⁿ : ∀ {st st'' n m} → st ↦[ n + m ] st''
            → ∃[ st' ] (st ↦[ n ] st' × st' ↦[ m ] st'')
    split↦ⁿ {n = 0} {m} rs = _ , ◾ , rs
    split↦ⁿ {n = suc n} {m} (r ∷ rs) with split↦ⁿ {n = n} {m} rs
    ... | st' , st↦ⁿst' , st'↦ᵐst'' = st' , (r ∷ st↦ⁿst') , st'↦ᵐst''

    same-trace : ∀ {st₀ m n stₙ}
      → st₀ ↦[ n ] stₙ
      → m ≡ n
      → st₀ ↦[ m ] stₙ
    same-trace {st₀} {m} {.m} {stₙ} st₀↦stₙ refl = st₀↦stₙ

    ≤-+ : ∀ {m} {N}
      → m ≤ N
      → ∃[ rest ] (m + rest ≡ N)
    ≤-+ {zero} {zero} m≤N = zero , refl
    ≤-+ {zero} {suc N} m≤N = suc N , refl
    ≤-+ {suc m} {suc N} (s≤s m≤N) with ≤-+ m≤N
    ... | rest , refl = rest , refl

  s1-1 : ∀ N st₀
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → ∀ m rest → m + rest ≡ N → ∃[ stₘ ] (st₀ ↦[ m ] stₘ)
  s1-1 N st₀ (stₙ , st₀↦stₙ) m rest refl with split↦ⁿ {st₀} {stₙ} {m} {rest}  st₀↦stₙ
  ... | stₘ , st₀↦stₘ , stₘ↦stₙ = stₘ , st₀↦stₘ

  s1-2 : ∀ N st₀
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → ∀ m → m ≤  N → ∃[ stₘ ] (st₀ ↦[ m ] stₘ)
  s1-2 N st₀ (stₙ , st₀↦stₙ) m m≤N with ≤-+ m≤N
  ... | rest , refl with split↦ⁿ {st₀} {stₙ} {m} {rest}  st₀↦stₙ
  ... | stₘ , st₀↦stₘ , stₘ↦stₙ = stₘ , st₀↦stₘ

  s1-3 : ∀ N st₀
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → ∀ m → ∃[ stₘ ] (m ≤  N → st₀ ↦[ m ] stₘ)
  s1-3 N st₀ (stₙ , st₀↦stₙ) m = {!!}

  s2-helper : ∀ N st₀
    → ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → ∀ m → m ≤  N → Fin N
  s2-helper N st₀ St-Fin ∃st₀↦stₙ m m≤N with s1-2 N st₀ ∃st₀↦stₙ m m≤N
  ... | ∃st₀↦stₘ = to St-Fin (m ,  ∃st₀↦stₘ)
  
  s2 : ∀ N st₀
    → ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → ∀ m → m ≤  N → ℕ
  s2 N st₀ St-Fin ∃st₀↦stₙ m m≤N = toℕ (s2-helper N st₀ St-Fin ∃st₀↦stₙ m m≤N)

  s3 : ∀ N st₀
    → ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → ∀ (m : ℕ) → ℕ
  s3 N st₀ St-Fin ∃stₙ m with m ≤? N
  ... | .true because ofʸ p = s2 N st₀ St-Fin ∃stₙ m p
  ... | .false because ofⁿ ¬p = 0

  s3<N : ∀ N st₀
    → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
    → (∃stₙ : ∃[ stₙ ] (st₀ ↦[ N ] stₙ))
    → ∀ (m : ℕ) → m ≤ N → s3 N st₀ St-Fin ∃stₙ m < N
  s3<N N st₀ St-Fin ∃stₙ m m≤N = {!!}

  s4 : ∀ N st₀
    → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
    → (∃stₙ : ∃[ stₙ ] (st₀ ↦[ N ] stₙ))
    → ∀ m n → m ≤ N → n ≤ N → s3 N st₀ St-Fin ∃stₙ m  ≡ s3 N st₀ St-Fin ∃stₙ n
    → m ≡ n
  s4 N st₀ St-Fin ∃stₙ m n m≤N n≤N eql with m ≤? N
  ... | .false because ofⁿ ¬p = {!!}
  ... | .true because ofʸ p with n ≤? N
  ... | .false because ofⁿ ¬p = {!!}
  ... | .true because ofʸ p₁ = {!!}
 
  pigeonhole-helper : ∀ {N st₀}
    → (St-Fin :  ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
    → (st₀↦ⁿstₙ : ∃[ stₙ ] (st₀ ↦[ N ] stₙ))
    → (∀ n → (n≤N : n ≤ N) → (s3 N st₀ St-Fin (st₀↦ⁿstₙ) n ) < N)
  pigeonhole-helper {N} {st₀} St-Fin st₀↦ⁿstₙ n n≤N = s3<N N st₀ St-Fin (st₀↦ⁿstₙ) n n≤N

  Finite-State-Termination-At-N : ∀ {N st₀}
    → ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ) → ⊥
  Finite-State-Termination-At-N {N} {st₀} St-Fin st₀-initial (stₙ , st₀↦stₙ)
    with pigeonhole N (s3 N st₀ St-Fin (stₙ , st₀↦stₙ)) (pigeonhole-helper {N} {st₀} St-Fin (stₙ , st₀↦stₙ) ) 
  ... | m , n , m<n , n≤N , tofm≡tofn with ≤-trans (<⇒≤  m<n) n≤N
  ... | m≤N with s1-2 N st₀ (stₙ , st₀↦stₙ) m m≤N
  ... | stₘ , st₀↦stₘ with s1-2 N st₀ (stₙ , st₀↦stₙ) n n≤N -- Step→Trace (st₀↦ᴺ↦stₙ) n
  ... | stₙ₁ , st₀↦stₙ₁  with NoRepeat st₀-initial m<n st₀↦stₘ  st₀↦stₙ₁
  ... | stₘ≢stₙ with s4 N st₀ St-Fin (stₙ , st₀↦stₙ) m n m≤N n≤N tofm≡tofn -- from-reverse stₘ stₙ N St-Fin  tofm≡tofn
  ... | stₘ≡stₙ = {!!} -- stₘ≢stₙ stₘ≡stₙ

  private
    [n]→* : ∀ {n st₀ stₙ}
      → st₀ ↦[ n ] stₙ
      → st₀ ↦* stₙ
    [n]→* {0} {st₀} {.st₀} ◾ = ◾
    [n]→* {suc n} {st₀} {stₙ} (st₀↦st₁ ∷ st₁↦ⁿstₙ) = st₀↦st₁ ∷ [n]→* st₁↦ⁿstₙ
    
    cd-1 : ∀ {cd} {m} {N}
      → suc (cd + m) ≡ N
      → cd + (m + 1) ≡ N
    cd-1 {cd} {m} eql  with sym(+-assoc cd m 1)    -- trans (+-assoc m 1 cd) eql
    ... | cd+[m+1]≡cd+m+1 with  +-comm (cd + m) 1 
    ... | cd+m+1≡suc[cd+m] = trans (trans cd+[m+1]≡cd+m+1  cd+m+1≡suc[cd+m]) eql

  Finite-Reachable-State-Termination-CountDown : ∀ {N st₀}
    → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
    → is-initial st₀
    → ∀ cd m  stₘ → cd + m ≡ N → st₀ ↦[ m ] stₘ
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)

  Finite-Reachable-State-Termination-CountDown {N} {st₀} St-Fin st₀-initial (suc cd) m stₘ sum-eql st₀↦ᵐstₘ with has-next stₘ
  ... | .false because ofⁿ ¬p = stₘ , [n]→* st₀↦ᵐstₘ , ¬p
  ... | .true because ofʸ (stₘ₊₁ , stₘ↦stₘ₊₁) with cd-1 {cd} sum-eql
  ... | sum-eql with st₀↦ᵐstₘ ++↦ⁿ (stₘ↦stₘ₊₁ ∷ ◾)
  ... | st₀↦stₘ₊₁ = Finite-Reachable-State-Termination-CountDown  {N} {st₀} St-Fin st₀-initial cd (m + 1) stₘ₊₁ sum-eql st₀↦stₘ₊₁ 

  Finite-Reachable-State-Termination-CountDown {N} {st₀} St-Fin st₀-initial 0 m stₘ refl st₀↦ᵐstₘ with Finite-State-Termination-At-N {N} {st₀} St-Fin st₀-initial  (stₘ  , st₀↦ᵐstₘ) 
  ... | ()
  
  Finite-Reachable-State-Termination : ∀ {N st₀}
    → (St-Fin : ∃[ m ] ∃[ stₘ ] (st₀ ↦[ m ] stₘ) ⤖ Fin N)
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)
  Finite-Reachable-State-Termination {N} {st₀} St-Fin st₀-initial
    = Finite-Reachable-State-Termination-CountDown {N} {st₀} St-Fin st₀-initial N 0 st₀ (+-identityʳ N) ◾

