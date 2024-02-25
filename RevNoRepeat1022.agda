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
-- open import Function.Bijection.Bijection using ( to )
open import Data.Fin using ( Fin ; toℕ ; fromℕ<)
open import Relation.Nullary

open import Pigeonhole


module RevNoRepeat1022 {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine.RevMachine M
  open import RevNoRepeat M

--    st₀    ↦    st₁    ↦    st₂    ↦    st₃    ↦    stₙ₋₁      ↦      stₙ
--    0           1           2           3           n-1               n (≡N) ∀ n → n ≤ N
--    st₀↦[0]st₀  st₀↦[1]st₁  st₀↦[2]st₂  st₀↦[3]st₃  st₀↦[n-1]stₙ₋₁    st₀↦[n]stₙ
--    FinN        FinN        FinN        FinN        FinN              FinN
--    toℕ(FinN)     toℕ(FinN)     toℕ(FinN)     toℕ(FinN)     toℕ(FinN)           toℕ(FinN)

--    f( n ) => st₀ ↦[n] stₙ 得到 stₙ ， 經過  State ⤖ Fin N 轉換 stₙ 為 FinN ，toℕ FinN 轉換成結果

  -- 頭尾定義
  
  is-not-stuck : State → Set _
  is-not-stuck st = ∃[ st' ] (st ↦ st')

  
----------------------

----------------------
  -- 把 State ⤖ Fin N 中的 to 跟 from 拉出來用
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
  same₁ : ∀ {st₀ m n stₙ}
    → st₀ ↦[ n ] stₙ
    → m ≡ n
    → st₀ ↦[ m ] stₙ
  same₁ {st₀} {m} {.m} {stₙ} st₀↦stₙ refl = st₀↦stₙ

-- with cong (λ x → (st₀ ↦[ x ] stₙ)) m≡n
--   ... | a = {!!}

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
  ... | symcd+m with split↦ⁿ {st₀} {stₙ} {m} {cd} (same₁ st₀↦stₙ (trans (+-comm m cd ) cd+m≡n ))
  ... | stₘ , st₀↦stₘstₘ , _ = stₘ , st₀↦stₘstₘ

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
  --              ∃-syntax (λ stₘ → suc m ≤ suc N → st₀ ↦[ suc m ] stₘ)

  Step→State : ∀ {N st₀}
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → State
  Step→State {.0} {.stₙ} (stₙ , ◾) zero = stₙ
  Step→State {.0} {.stₙ} (stₙ , ◾) (suc m) = stₙ
  Step→State {.(suc _)} {st₀} (stₙ , (st₀↦st₁ ∷ st₁↦ⁿstₙ)) zero = st₀
  Step→State {.(suc _)} {st₀} (stₙ , (st₀↦st₁ ∷ st₁↦ⁿstₙ)) (suc m) = Step→State  (stₙ , (st₁↦ⁿstₙ)) (m) 
{-
  Step→State {N} {st₀} (stₙ , st₀↦stₙ) m with m ≤? N
  ... | .false because ofⁿ ¬m≤N = st₀
  ... | .true because ofʸ m≤N with getCd′ m≤N
  ... | cd , m+cd≡N = proj₁ ( split↦ⁿ {st₀} {stₙ} {m} {cd} (same₁ st₀↦stₙ m+cd≡N) )
-}
  Step→Fin : ∀ {N st₀}
    → State ⤖ Fin N
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → Fin N
  Step→Fin {N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m = to St-Fin (proj₁ (Step→Trace {N} {st₀} (stₙ , st₀↦ⁿstₙ) m))
  

  Step→ℕ : ∀ {N st₀}
    → State ⤖ Fin N
    → ∃[ stₙ ] (st₀ ↦[ N ] stₙ)
    → (m : ℕ) → ℕ

  Step→ℕ {N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m = toℕ (Step→Fin {N} {st₀} St-Fin (stₙ , st₀↦ⁿstₙ) m)

----------------------
  -- Others
  FinN<N : ∀ {N : ℕ} (fn : Fin N)
    → (toℕ fn) < N
  FinN<N Fin.zero = s≤s z≤n
  FinN<N (Fin.suc fn) = s≤s (FinN<N fn)
  
  sub1-1 : ∀ {N st₀ stₙ}
    → (St-Fin : State ⤖ Fin N)
    → (st₀↦ᴺstₙ : st₀ ↦[ N ] stₙ)
    → (∀ n → (n≤N : n ≤ N) → (Step→ℕ St-Fin (stₙ , st₀↦ᴺstₙ) n ) < N)
  sub1-1 {N} {st₀} {stₙ} St-Fin st₀↦ᴺstₙ n n≤N with (Step→Fin St-Fin (stₙ , st₀↦ᴺstₙ) n)
  ... | FinN  = FinN<N FinN

{- with n ≤? N
  ... | .true because ofʸ n≤N = FinN<N FinN -- FinN<N (to St-Fin (proj₁ (SubTrace st₀ n N stₙ st₀↦ᴺstₙ (getCd n≤N))))
  ... | .false because ofⁿ ¬p = {!!} -- FinN<N (to St-Fin st₀)  
-}

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
{-
-- n₁ 與 m₁ 都對應到一個 < N 的 State，那麼他們to過去應該要是不同的 Fin N
-- 然後 tofm≡tofn ，所以得到矛盾

  sub1-3-1-1-1 : ∀ {N} {fm : Fin N}
    → fromℕ< (FinN<N fm) ≡ fm
  sub1-3-1-1-1 {.(suc _)} {Fin.zero} = refl
  sub1-3-1-1-1 {.(suc _)} {Fin.suc fm} = cong Fin.suc sub1-3-1-1-1

  sub1-3-1-1 : ∀ {N} {fm fn : Fin N}
    → toℕ fm ≡ toℕ fn
    → fm ≡ fn
  sub1-3-1-1 {.(suc _)} {Fin.zero} {Fin.zero} tofm≡tofn = refl
  sub1-3-1-1 {.(suc _)} {Fin.suc fm} {Fin.suc fn} tofm≡tofn = {!!}

  sub1-3-1-2 : ∀ {N stₘ stₙ}
    → (St-Fin : State ⤖ Fin N)
    → to St-Fin stₘ ≡ to St-Fin stₙ
    → stₘ ≡ stₙ
  sub1-3-1-2 {N} {stₘ} {stₙ} St-Fin fm≡fn with to-from St-Fin stₘ
  ... | stₘ≡stₘ with to-from St-Fin stₙ
  ... | stₙ≡stₙ with cong (λ x → from St-Fin x) fm≡fn
  ... | stₘ≡stₙ = trans (trans (sym stₘ≡stₘ) stₘ≡stₙ) stₙ≡stₙ
    
  sub1-3-1-3 : ∀ {N m n st₀}
    → m ≤ N → n ≤ N
    → (ex : ∃[ stₙ ] (st₀ ↦[ N ] stₙ))
    → Step→State ex m ≡ Step→State ex n
    → m ≡ n
  sub1-3-1-3 {N} {m} {n} {st₀} m≤N n≤N ex b≡d = {!!}
  -}
{-
  when m ≤ N → ∃[ cd ] (m+cd≡N)

  Step→State ex m ≡ Step→State ex n
  → proj₁ ( split↦ⁿ {st₀} {stₙ} {m} {cd₁} (st₀↦stₙ) ≡ proj₁ ( split↦ⁿ {st₀} {stₙ} {n} {cd} (st₀↦stₙ)
  -- cd 不同？
  → 
-}

{- with m ≤? N
  ... | .false because ofⁿ ¬p = {!!}
  ... | .true because ofʸ p with tmpState {N} {st₀} {m} m≤N ex (SubTrace st₀ m N ex (getCd p))
  ... | a≡b with n ≤? N
  ... | .false because ofⁿ ¬p₁ = {!!}
  ... | .true because ofʸ p with tmpState {N} {st₀} {n} n≤N ex (SubTrace st₀ n N ex (getCd p))
  ... | c≡d with trans (trans a≡b b≡d) (sym c≡d)
  ... | a≡c with m ≤? N
  ... | .false because ofⁿ ¬p₂ = {!!}
  ... | .true because ofʸ p₂ with n ≤? N 
  ... | .false because ofⁿ ¬p₃ = {!!}
  ... | .true because ofʸ p₃ = {!!}
-}


-- {!tmpState {N} {st₀} {m} m≤N ex ?!}
{-    
  sub1-3-1 : ∀ {N m n st₀ stₙ}
    → (St-Fin : State ⤖ Fin N)
    → (st₀↦ⁿstₙ : st₀ ↦[ N ] stₙ)
    → m ≤ N → n ≤ N
    → Step→ℕ St-Fin (stₙ , st₀↦ⁿstₙ) m ≡ Step→ℕ St-Fin (stₙ , st₀↦ⁿstₙ) n
    → m ≡ n
  sub1-3-1 {N} {m} {n} {st₀} {stₙ} St-Fin st₀↦ⁿstₙ m≤N n≤N tofm≡tofn with sub1-3-1-1 tofm≡tofn
  ... | fm≡fn with sub1-3-1-2 St-Fin fm≡fn
  ... | stₘ≡stₙ with sub1-3-1-3 m≤N n≤N (stₙ , st₀↦ⁿstₙ) stₘ≡stₙ
  ... | m≡n = m≡n
-}
{- with m ≤? N
  ... | .false because ofⁿ ¬p = {!!}
  ... | .true because ofʸ m≤N′ with n ≤? N
  ... | .false because ofⁿ ¬p₁ = {!!}
  ... | .true because ofʸ n≤N′ = {!!}
-}
{-
  sub1-3 : ∀ {m n N st₀ stₙ}
    → (St-Fin : State ⤖ Fin N)
    → m < n → n ≤ N
    → (st₀↦ⁿstₙ : st₀ ↦[ N ] stₙ)
    → Step→ℕ St-Fin (stₙ , st₀↦ⁿstₙ) m ≢ Step→ℕ St-Fin (stₙ , st₀↦ⁿstₙ) n
  sub1-3 {m} {n} {N} {st₀} {stₙ} St-Fin m<n n≤N st₀↦ⁿstₙ tofm≡tofn with ≤-trans (<→≤ m<n) n≤N
  ... | m≤N with sub1-3-1 {N} {m} {n} St-Fin st₀↦ⁿstₙ m≤N n≤N tofm≡tofn
  ... | a = (<→≢ m<n) a
-}

{- with n ≤? N
  ... | .false because ofⁿ ¬p = ¬p n≤N
  ... | .true because ofʸ p with m ≤? N
  ... | .false because ofⁿ ¬p₁ = ¬p₁ (≤-trans (<→≤ m<n) n≤N)
  ... | .true because ofʸ p₁ = {!!}
-}

  from-toℕ : ∀ N m → (m<N : m < N)
    → toℕ (fromℕ< {m} {N} m<N) ≡ m
  from-toℕ (suc N) zero m<N = refl
  from-toℕ (suc N) (suc m) m<N = cong suc (from-toℕ N m (≤-pred m<N))

  to-fromℕ : ∀ N (fn : Fin N) -- → (m<N : m < N
    → fromℕ< {toℕ fn} (FinN<N fn) ≡ fn
  to-fromℕ (suc N) Fin.zero = refl
  to-fromℕ (suc N) (Fin.suc fn) = cong Fin.suc (to-fromℕ N fn)

{-
  tmp2 : ∀ N (fm fn : Fin N)
    → toℕ fm ≡ toℕ fn
    → (FinN<N fm) ≡ (FinN<N fn)
  tmp2 N fm fn eql = ?
-}
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

  to-eql : ∀ {stₘ stₙ N}
    → (St-Fin : State ⤖ Fin N)
    → to St-Fin stₘ ≡ to St-Fin stₙ
    → stₘ ≡ stₙ
  to-eql {stₘ} {stₙ} {_} St-Fin eql with to-from St-Fin stₘ
  ... | a≡stₘ with to-from St-Fin stₙ
  ... | b≡stₙ with cong (from St-Fin) eql
  ... | a≡b = trans (trans (sym a≡stₘ) a≡b) b≡stₙ

  -- fromℕ< : ∀ {m n} → m ℕ.< n → Fin n
  from-reverse : ∀ stₘ stₙ N
    → (St-Fin : State ⤖ Fin N)
    → toℕ (to St-Fin stₘ) ≡ toℕ (to St-Fin stₙ)
    → stₘ ≡ stₙ
  from-reverse stₘ stₙ N St-Fin eql with toℕ→Fin eql
  ... | to-stₘ≡to-stₙ = to-eql St-Fin to-stₘ≡to-stₙ

  sub1 : ∀ {N m st₀ stₙ}
    → State ⤖ Fin N
    → is-initial st₀
    → m ≡ N
    → st₀ ↦[ N ] stₙ → ⊥

  sub1 {N} {m} {st₀} {stₙ} St-Fin st₀-initial m≡N st₀↦ⁿ↦stₙ with sub1-1 {N} {st₀} St-Fin (st₀↦ⁿ↦stₙ) 
  ... | line2 with pigeonhole (N) (Step→ℕ St-Fin (stₙ , st₀↦ⁿ↦stₙ))  line2 
  ... | m₁ , n₁ , m₁<n₁ , n₁≤N , tofn₁≡tofm₁ with ≤-trans (<→≤ m₁<n₁) n₁≤N
  ... | m₁≤N with Step→Trace {N} {st₀} (stₙ , st₀↦ⁿ↦stₙ ) m₁
  ... | stₘ₁ , trₘ  with Step→Trace {N} {st₀} (stₙ , st₀↦ⁿ↦stₙ) n₁
  ... | stₙ₁ , trₙ with NoRepeat {st₀} {stₘ₁} {stₙ₁} {m₁} {n₁} st₀-initial m₁<n₁ (trₘ m₁≤N) (trₙ n₁≤N)
  ... | a = a (sym (from-reverse stₙ₁ stₘ₁ N St-Fin  tofn₁≡tofm₁ ) )

-- (sub1-3 St-Fin m₁<n₁ n₁≤N (same₁ st₀↦ⁿ↦stₙ (sym m≡N))) (sym tofn₁≡tofm₁)
{- with n₁ ≤? N


  ... | .false because ofⁿ ¬p = ¬p n₁≤N
  ... | .true because ofʸ p with m₁ ≤? N
  ... | .false because ofⁿ ¬p = ¬p (sub1-2 m₁<n₁ n₁≤N)
  ... | .true because ofʸ p₁ with Step→ℕ St-Fin (stₙ , same₁ st₀↦ⁿ↦stₙ (sym m≡N)) n₁
  ... | tofn₁ with Step→ℕ St-Fin (stₙ , same₁ st₀↦ⁿ↦stₙ (sym m≡N)) m₁
  ... | tofm₁ = {!(sub1-3 St-Fin m₁<n₁ n₁≤N (same₁ st₀↦ⁿ↦stₙ (sym m≡N))) tofn₁≡tofm₁ !}

-}

  sub2 : ∀ {m n}
    → m + 0 ≡ n
    → m ≡ n
  sub2 {m} {n} m+0≡n = trans (sym (+-comm m 0)) m+0≡n 

  sub8 : ∀ {n st₀ stₙ}
    → st₀ ↦[ n ] stₙ
    → st₀ ↦* stₙ
  sub8 {0} {st₀} {.st₀} ◾ = ◾
  sub8 {suc n} {st₀} {stₙ} (st₀↦st₁ ∷ st₁↦ⁿstₙ) = st₀↦st₁ ∷ sub8 st₁↦ⁿstₙ

  cd-1 : ∀ {m} {cd} {N}
    → (m) + (suc cd) ≡ N
    → (m + 1) + (cd) ≡ N
  cd-1 {m} {cd} eql = trans (+-assoc m 1 cd) eql -- trans (sym (+-suc m cd)) eql 


  p1 : ∀ {N st₀}
    → State ⤖ Fin N
    → is-initial st₀
    → ∀ m cd stₘ → m + cd ≡ N → st₀ ↦[ m ] stₘ
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)

  p1 {N} {st₀} St-Fin st₀-initial m (suc cd) stₘ sum-eql st₀↦ᵐstₘ with has-next stₘ
  ... | .true because ofʸ (stₘ₊₁ , stₘ↦stₘ₊₁) = p1 {N} {st₀} St-Fin st₀-initial (m + 1) cd stₘ₊₁ (cd-1 sum-eql)
    (_++↦ⁿ_ {n = m} {m = 1} st₀↦ᵐstₘ (stₘ↦stₘ₊₁ ∷ ◾))
  ... | .false because ofⁿ ¬p = stₘ , sub8 st₀↦ᵐstₘ , ¬p

  p1 {N} {st₀} St-Fin st₀-initial m 0 stₘ m+0≡N st₀↦ᵐstₘ with sub2 m+0≡N
  ... | m≡N with sub1 {N} {m} {st₀} {stₘ} St-Fin st₀-initial m≡N (same₁ st₀↦ᵐstₘ (sym m≡N))
  ... | ()

-- p2 : 可能是無限或有限的State ，對每個initial state，reachable state是有限的

-- Pi/

  real-p1 : ∀ {N st₀}
    → State ⤖ Fin N
    → is-initial st₀
    → ∃[ stₙ ] (st₀ ↦* stₙ × is-stuck stₙ)
  real-p1 {N} {st₀} St-Fin st₀-initial = p1 {N} {st₀} St-Fin st₀-initial 0 N st₀ refl ◾
--  aa {N = N} {m = m} = p1 {N = N} {m = m} {cd = proj₁ (aa-helper m N {!!})} {proj₂ (aa-helper m N {!!})}

