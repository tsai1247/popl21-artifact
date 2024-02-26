import Level as L
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; cong₂ ; cong-app; subst)
open import Data.Product
open import Data.Empty
open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat
open import Data.Nat.Properties using ( +-suc ; +-comm ; +-assoc ; <-trans ; ≤-trans)
open import RevMachine

open import Function.Bijection using ( _⤖_ ; Bijection )
open import Data.Fin using ( Fin ; toℕ ; fromℕ<)
open import Relation.Nullary

open import Pigeonhole

module RevTerminate {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine.RevMachine M
  open import RevNoRepeat M

----------------------
  -- 把 State ⤖ Fin N 中的 to 跟 from 拉出來用
  
  to : ∀ {N st₀} → (∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N ) → ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) → Fin N
  to record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = bijective } ∃stₘ[] = _⟨$⟩_ ∃stₘ[]

  from : ∀ {N st₀} → (∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N ) → Fin N → ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ)
  from record { to = to ; bijective = record { injective = injective ; surjective = record { from = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; right-inverse-of = right-inverse-of } } } fn = _⟨$⟩_ fn

  to-from : ∀ {N st₀}
    → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → (∃stₘ[] : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ))
    → from St-Fin (to St-Fin ∃stₘ[]) ≡ ∃stₘ[]
  to-from record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = record { injective = injective ; surjective = record { from = from ; right-inverse-of = right-inverse-of } } } ∃stₘ[] = injective (right-inverse-of (_⟨$⟩_ ∃stₘ[]))

  from-to : ∀ {N st₀}
    → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → (fn : Fin N)
    → to St-Fin (from St-Fin fn) ≡ fn
  from-to record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = record { injective = injective ; surjective = record { from = from ; right-inverse-of = right-inverse-of } } } st = right-inverse-of st


  private
    same-trace : ∀ {st₀ m n stₙ}
      → st₀ ↦[ n ] stₙ
      → m ≡ n
      → st₀ ↦[ m ] stₙ
    same-trace {st₀} {m} {.m} {stₙ} st₀↦stₙ refl = st₀↦stₙ

    split↦ⁿ : ∀ {st st'' n m} → st ↦[ n + m ] st''
      → ∃[ st' ] (st ↦[ n ] st' × st' ↦[ m ] st'')
    split↦ⁿ {n = 0} {m} rs = _ , ◾ , rs
    split↦ⁿ {n = suc n} {m} (r ∷ rs) with split↦ⁿ {n = n} {m} rs
    ... | st' , st↦ⁿst' , st'↦ᵐst'' = st' , (r ∷ st↦ⁿst') , st'↦ᵐst''

  SubTrace : ∀ st₀ m n
    → ∃[ stₙ ] (st₀ ↦[ n ] stₙ)
    → ∃[ cd ] ( cd + m ≡ n)
    → ∃[ stₘ ] (st₀ ↦[ m ] stₘ)
  SubTrace st₀ m n (stₙ , st₀↦stₙ) (cd , cd+m≡n) with sym cd+m≡n
  ... | symcd+m with (same-trace st₀↦stₙ (trans (+-comm m cd ) cd+m≡n ))
  ... | st₀↦[cd+m]stₙ with split↦ⁿ {st₀} {stₙ} {m} {cd} st₀↦[cd+m]stₙ
  ... | stₘ , st₀↦stₘstₘ , _ = stₘ , st₀↦stₘstₘ

  private
    Step→Trace-helper : ∀ {m N st₀ st₁ stₘ}
      → st₀ ↦ st₁
      → (m ≤ N → st₁ ↦[ m ] stₘ)
      → (suc m ≤ suc N → st₀ ↦[ suc m ] stₘ)
    Step→Trace-helper st₀↦st₁ m≤N→st₁↦stₘ (s≤s m≤N) = st₀↦st₁ ∷ m≤N→st₁↦stₘ m≤N

  Step→Trace : ∀ {N st₀}
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → ∃[ stₘ ] (m ≤ N → st₀ ↦[ m ] stₘ)
  Step→Trace {0} {st₀} (stₙ , st₀↦ᴺstₙ) 0 = stₙ , λ _ → st₀↦ᴺstₙ
  Step→Trace {0} {st₀} (stₙ , st₀↦ᴺstₙ) (suc m) = stₙ , λ ()
  Step→Trace {suc N} {st₀} (stₙ , st₀↦ᴺstₙ) zero = st₀ , λ _ → ◾
  Step→Trace {suc N} {st₀} (stₙ , (st₀↦st₁ ∷ st₁↦ᴺstₙ)) (suc m) with Step→Trace (stₙ , st₁↦ᴺstₙ) m
  ... | stₘ , snd = stₘ , Step→Trace-helper st₀↦st₁ snd 

  Step→Fin : ∀ {N st₀}
    → (∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → Fin N
  -- not sure
  Step→Fin {zero} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m = to St-Fin (st₀ , 0  , ◾)

  Step→Fin {suc N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m with Step→Trace (stₙ , st₀↦ⁿstₙ) m 
  ... | stₘ , m≤N→st₀↦stₘ with m ≤? suc N
  ... | .true because ofʸ p = to St-Fin (stₘ , m , m≤N→st₀↦stₘ p)
  ... | .false because ofⁿ ¬p = Fin.zero {N} -- Fin.zero


  Step→ℕ : ∀ {N st₀}
    → (∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → ℕ

  Step→ℕ {N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m = toℕ (Step→Fin {N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m )

----------------------
  -- Others
  private
    FinN<N : ∀ {N : ℕ} (fn : Fin N)
      → (toℕ fn) < N
    FinN<N Fin.zero = s≤s z≤n
    FinN<N (Fin.suc fn) = s≤s (FinN<N fn)
  
  sub1-1 : ∀ {N st₀ stₙ}
    → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → (st₀↦ᴺstₙ : st₀ ↦[ N ] stₙ)
    → (∀ n → (n≤N : n ≤ N) → (Step→ℕ St-Fin (stₙ , st₀↦ᴺstₙ) n) < N)
  sub1-1 {N} {st₀} {stₙ} St-Fin st₀↦ᴺstₙ n n≤N with (Step→Fin St-Fin (stₙ , st₀↦ᴺstₙ) n )
  ... | FinN  = FinN<N FinN

  private
    <→≤ : ∀ {m n}
      → m < n → m ≤ n
    <→≤ {zero} {n} m<n = z≤n
    <→≤ {suc m} {suc n} (s≤s m<n) = s≤s (<→≤ m<n)

    <-irreflexive : ∀(n : ℕ) → ¬ (n < n)
    <-irreflexive zero ()
    <-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n

    <→≢ : ∀{m n : ℕ}
      → m < n → ¬ m ≡ n 
    <→≢ {suc m} .{suc _} (s≤s _m<n) refl = <-irreflexive m _m<n

    to-fromℕ : ∀ N (fn : Fin N)
      → fromℕ< {toℕ fn} (FinN<N fn) ≡ fn
    to-fromℕ (suc N) Fin.zero = refl
    to-fromℕ (suc N) (Fin.suc fn) = cong Fin.suc (to-fromℕ N fn)

    ss : ∀ {m} {n}
      → suc m ≡ suc n
      → m ≡ n
    ss refl = refl

    toℕ→Fin : ∀ {N} {fm fn : Fin N}
      → toℕ fm ≡ toℕ fn
      → fm ≡ fn
    toℕ→Fin {N} {fm} {fn} eql with to-fromℕ N fn
    ... | from-to-fn≡fn with to-fromℕ N fm
    toℕ→Fin {_} {Fin.zero} {Fin.zero} eql | from-to-fn≡fn | from-to-fm≡fm = refl
    toℕ→Fin {suc n} {Fin.suc fm} {Fin.suc fn} eql | from-to-fn≡fn | from-to-fm≡fm = cong Fin.suc (toℕ→Fin {n} {fm} {fn} (ss eql) )

    to-eql : ∀ {stₘ stₙ st₀ N}
      → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
      → to St-Fin (stₘ , {!!} , {!!}) ≡ to St-Fin (stₙ , {!!} , {!!})
      → ((stₘ , {!!} , {!!})) ≡ ((stₙ , {!!} , {!!}))
    to-eql = {!!} -- {stₘ} {stₙ} {_} St-Fin eql with to-from St-Fin stₘ
--    ... | a≡stₘ with to-from St-Fin stₙ
--    ... | b≡stₙ with cong (from St-Fin) eql
--    ... | a≡b = trans (trans (sym a≡stₘ) a≡b) b≡stₙ


  from-reverse : ∀ st₀ stₘ stₙ N
    → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → toℕ (to St-Fin stₘ) ≡ toℕ (to St-Fin stₙ)
    → stₘ ≡ stₙ
  from-reverse st₀ stₘ stₙ N St-Fin eql with toℕ→Fin eql
  ... | to-stₘ≡to-stₙ = {!!} --  to-eql St-Fin to-stₘ≡to-stₙ


  stₙ→⊥ : ∀ {N st₀ stₙ}
    → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → is-initial st₀
    → st₀ ↦[ N ] stₙ → ⊥

  stₙ→⊥ {N} {st₀} {stₙ} St-Fin st₀-initial st₀↦ⁿ↦stₙ with sub1-1 {N} {st₀} St-Fin (st₀↦ⁿ↦stₙ) 
  ... | line2 with pigeonhole (N) (Step→ℕ St-Fin (stₙ , st₀↦ⁿ↦stₙ)) line2
  ... | m₁ , n₁ , m₁<n₁ , n₁≤N , tofn₁≡tofm₁ with ≤-trans (<→≤ m₁<n₁) n₁≤N
  ... | m₁≤N with Step→Trace {N} {st₀} (stₙ , st₀↦ⁿ↦stₙ ) m₁
  ... | stₘ₁ , trₘ  with Step→Trace {N} {st₀} (stₙ , st₀↦ⁿ↦stₙ) n₁
  ... | stₙ₁ , trₙ with NoRepeat {st₀} {stₘ₁} {stₙ₁} {m₁} {n₁} st₀-initial m₁<n₁ (trₘ m₁≤N) (trₙ n₁≤N)
  ... | a = {!a (sym (from-reverse st₀ ? ? N St-Fin ?)) !}
  -- a (sym (from-reverse st₀ stₙ₁ stₘ₁ N St-Fin  tofn₁≡tofm₁ ) ) 

  private
    add-zero-eql : ∀ {m n}
      → m + 0 ≡ n
      → m ≡ n
    add-zero-eql {m} {n} m+0≡n = trans (sym (+-comm m 0)) m+0≡n 

    [n]→* : ∀ {n st₀ stₙ}
      → st₀ ↦[ n ] stₙ
      → st₀ ↦* stₙ
    [n]→* {0} {st₀} {.st₀} ◾ = ◾
    [n]→* {suc n} {st₀} {stₙ} (st₀↦st₁ ∷ st₁↦ⁿstₙ) = st₀↦st₁ ∷ [n]→* st₁↦ⁿstₙ

    cd-1 : ∀ {m} {cd} {N}
      → (m) + (suc cd) ≡ N
      → (m + 1) + (cd) ≡ N
    cd-1 {m} {cd} eql = trans (+-assoc m 1 cd) eql


  p2 : ∀ {N st₀}
    → (St-Fin : ∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → is-initial st₀
    → ∀ m cd stₘ → m + cd ≡ N → st₀ ↦[ m ] stₘ
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)

  p2 {N} {st₀} St-Fin st₀-initial m (suc cd) stₘ sum-eql st₀↦ᵐstₘ with has-next stₘ
  ... | .true because ofʸ (stₘ₊₁ , stₘ↦stₘ₊₁) = p2 {N} {st₀} St-Fin st₀-initial (m + 1) cd stₘ₊₁ (cd-1 sum-eql)
    (_++↦ⁿ_ {n = m} {m = 1} st₀↦ᵐstₘ (stₘ↦stₘ₊₁ ∷ ◾))
  ... | .false because ofⁿ ¬p = stₘ , [n]→* st₀↦ᵐstₘ , ¬p

  p2 {N} {st₀} St-Fin st₀-initial m 0 stₘ m+0≡N st₀↦ᵐstₘ with add-zero-eql m+0≡N
  ... | m≡N with stₙ→⊥ {N} {st₀} {stₘ} St-Fin st₀-initial (same-trace st₀↦ᵐstₘ (sym m≡N))
  ... | ()
  
-- p2 : 可能是無限或有限的State ，對每個initial state，reachable state是有限的

  real-p2 : ∀ {N st₀}
    → (∃[ stₘ ] ∃[ m ] (st₀ ↦[ m ] stₘ) ⤖ Fin N )
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)
  real-p2 {N} {st₀} St-Fin st₀-initial = p2 {N} {st₀} St-Fin st₀-initial 0 N st₀ refl ◾

