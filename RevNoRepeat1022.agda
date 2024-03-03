open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; trans ; sym ; cong )
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties using ( +-comm ; +-assoc ; +-identityʳ  ; +-cancelˡ-≡ ; ≤-trans ; <⇒≤)
open import Function.Bijection using ( _⤖_)
open import Data.Fin using ( Fin ; toℕ ; fromℕ<)
open import Relation.Nullary

open import RevMachine
open import Pigeonhole

module RevNoRepeat1022 {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine.RevMachine M
  open import RevNoRepeat M

----------------------
  -- ⤖ : Bijection
  -- 以下定義 to, from, to-from, from-to，簡化官方Bijection的對應方式
  -- 例如 to St-Fin state₁ 代表 state₁ 經由 St-Fin 這個Bijection對應到的 Fin 值
  private
    to : ∀ {N} → State ⤖ Fin N → State → Fin N
    to record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = bijective } st = _⟨$⟩_ st

    from : ∀ {N} → State ⤖ Fin N → Fin N → State
    from record { to = to ; bijective = record { injective = injective ; surjective = record { from = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; right-inverse-of = right-inverse-of } } } fn = _⟨$⟩_ fn

    to-from : ∀ {N}
      → (St-Fin : State ⤖ Fin (N))
      → (st : State)
      → from St-Fin (to St-Fin st) ≡ st
    to-from record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = record { injective = injective ; surjective = record { from = from ; right-inverse-of = right-inverse-of } } } st = injective (right-inverse-of (_⟨$⟩_ st))

    from-to : ∀ {N}
      → (St-Fin : State ⤖ Fin (N))
      → (fn : Fin N)
      → to St-Fin (from St-Fin fn) ≡ fn
    from-to record { to = record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } ; bijective = record { injective = injective ; surjective = record { from = from ; right-inverse-of = right-inverse-of } } } st = right-inverse-of st
----------------------
  -- 已知 st₀到stₙ之間有一條長度為N的路徑
  -- 給定一個整數m，在 m ≤ N 的情況下可以得到一條 st₀ 到 stₘ 的路徑
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

  -- 給定一個步數，可以得到對應的整數。該整數是從步數得到State後，經由Bijection對應到的Fin N
  Step→ℕ : ∀ {N st₀}
    → State ⤖ Fin N
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → ℕ
  Step→ℕ {N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m = toℕ (to St-Fin (proj₁ (Step→Trace {N} {st₀} (stₙ , st₀↦ⁿstₙ) m)))

----------------------
  -- Fin N 總是比N小的證明
  private
    FinN<N : ∀ {N : ℕ} (fn : Fin N)
      → (toℕ fn) < N
    FinN<N Fin.zero = s≤s z≤n
    FinN<N (Fin.suc fn) = s≤s (FinN<N fn)

  -- 鴿籠原理的關鍵部分：每個至多為N的步數經由 Bijection 對應到的值都小於N
  -- 根據鴿籠原理，可以得到這些步數中至少會有兩個相同
  pigeonhole-helper : ∀ {N st₀}
    → (St-Fin : State ⤖ Fin N)
    → (st₀↦ⁿstₙ : ∃[ stₙ ] (st₀ ↦[ N ] stₙ))
    → (∀ n → (n≤N : n ≤ N) → (Step→ℕ St-Fin (st₀↦ⁿstₙ) n ) < N)
  pigeonhole-helper St-Fin st₀↦ⁿstₙ n n≤N with to St-Fin (proj₁ (Step→Trace  st₀↦ⁿstₙ n))
  ... | FinN  = FinN<N FinN

  private
    to-fromℕ : ∀ N (fn : Fin N)
      → fromℕ< {toℕ fn} (FinN<N fn) ≡ fn
    to-fromℕ (suc N) Fin.zero = refl
    to-fromℕ (suc N) (Fin.suc fn) = cong Fin.suc (to-fromℕ N fn)

    toℕ→Fin : ∀ {N} {fm fn : Fin N}
      → toℕ fm ≡ toℕ fn
      → fm ≡ fn
    toℕ→Fin {suc N} {Fin.zero} {Fin.zero} refl = refl
    toℕ→Fin {suc N} {Fin.suc fm} {Fin.suc fn} eql with to-fromℕ N fn
    ... | from-to-fn≡fn with to-fromℕ N fm
    ... | from-to-fm≡fm  = cong Fin.suc (toℕ→Fin (+-cancelˡ-≡ 1 eql))

    to-eql : ∀ {stₘ stₙ N}
      → (St-Fin : State ⤖ Fin N)
      → to St-Fin stₘ ≡ to St-Fin stₙ
      → stₘ ≡ stₙ
    to-eql {stₘ} {stₙ} {_} St-Fin eql with to-from St-Fin stₘ
    ... | a≡stₘ with to-from St-Fin stₙ
    ... | b≡stₙ with cong (from St-Fin) eql
    ... | a≡b = trans (trans (sym a≡stₘ) a≡b) b≡stₙ

    from-reverse : ∀ stₘ stₙ N
      → (St-Fin : State ⤖ Fin N)
      → toℕ (to St-Fin stₘ) ≡ toℕ (to St-Fin stₙ)
      → stₘ ≡ stₙ
    from-reverse stₘ stₙ N St-Fin eql with toℕ→Fin eql
    ... | to-stₘ≡to-stₙ = to-eql St-Fin to-stₘ≡to-stₙ

  -- 證明當 State 走到N步是不可能的
  -- 使用鴿籠原理找到 m 與 n，他們都對應到相同的 Fin N ，往回對應到相同的 State。而NoRepeat告訴我們這並不可能
  Finite-State-Termination-At-N : ∀ {N st₀}
    → State ⤖ Fin N
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ) → ⊥

  Finite-State-Termination-At-N {N} {st₀} St-Fin st₀-initial st₀↦ᴺ↦stₙ with pigeonhole N (Step→ℕ St-Fin st₀↦ᴺ↦stₙ)  (pigeonhole-helper  St-Fin st₀↦ᴺ↦stₙ )
  ... | m , n , m<n , n≤N , tofm≡tofn with ≤-trans (<⇒≤  m<n) n≤N
  ... | m≤N with Step→Trace (st₀↦ᴺ↦stₙ ) m
  ... | stₘ , st₀↦stₘ with Step→Trace (st₀↦ᴺ↦stₙ) n
  ... | stₙ , st₀↦stₙ with NoRepeat st₀-initial m<n (st₀↦stₘ m≤N ) (st₀↦stₙ n≤N)
  ... | stₘ≢stₙ with from-reverse stₘ stₙ N St-Fin  tofm≡tofn
  ... | stₘ≡ₙ = stₘ≢stₙ  stₘ≡ₙ

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
    
  Finite-State-Termination-With-Countdown : ∀ {N st₀}
    → State ⤖ Fin N
    → is-initial st₀
    → ∀ cd m stₘ → cd + m ≡ N → st₀ ↦[ m ] stₘ
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)

  -- 如果沒有下一個state，則找到終止，否則會繼續往cd ≡ 0 的case 前進
  Finite-State-Termination-With-Countdown  St-Fin st₀-initial (suc cd) _ stₘ sum-eql st₀↦ᵐstₘ with has-next stₘ
  ... | _ because ofⁿ ¬p = stₘ , [n]→* st₀↦ᵐstₘ , ¬p
  ... | _ because ofʸ (stₘ₊₁ , stₘ↦stₘ₊₁) with cd-1 {cd} sum-eql
  ... | sum-eql with st₀↦ᵐstₘ ++↦ⁿ (stₘ↦stₘ₊₁ ∷ ◾)
  ... | st₀↦stₘ₊₁ =  Finite-State-Termination-With-Countdown St-Fin st₀-initial cd _ stₘ₊₁ sum-eql st₀↦stₘ₊₁
  
  -- 當 cd ≡ 0 ，得到 m ≡ N ，從 stₙ→⊥
  Finite-State-Termination-With-Countdown St-Fin st₀-initial 0 m stₘ refl st₀↦ᵐstₘ
    with Finite-State-Termination-At-N St-Fin st₀-initial (stₘ , st₀↦ᵐstₘ)
  ... | ()

  Finite-State-Termination : ∀ {N st₀}
    → State ⤖ Fin N
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)
  Finite-State-Termination {N} {st₀}  St-Fin st₀-initial = Finite-State-Termination-With-Countdown St-Fin st₀-initial N 0 st₀  (+-identityʳ N)  ◾

-- p2 : 可能是無限或有限的State ，對每個initial state，reachable state是有限的
  Finite-Reachable-State-Termination : ∀ {N st₀}
    → (St-Fin : ∃[ stₘ ] (st₀ ↦* stₘ) ⤖ Fin N)
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)
  Finite-Reachable-State-Termination {N} {st₀} St-Fin st₀-initial = {!!} 
