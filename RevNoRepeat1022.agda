import Level as L
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl; trans; sym; cong; cong-app; subst)
open import Data.Product
open import Data.Empty
open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat
open import Data.Nat.Properties using ( +-suc ; +-comm )
open import RevMachine
open import Function.Bijection using ( _⤖_ ; Bijection )
-- open import Function.Bijection.Bijection using ( to )
open import Data.Fin using ( Fin ; toℕ ; fromℕ<)
open import Relation.Nullary

open import Pigeonhole

module RevNoRepeat1022 {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine.RevMachine M

  is-initial : State → Set _
  is-initial st = ∄[ st' ] (st' ↦ st)
  
  is-not-stuck : State → Set _
  is-not-stuck st = ∃[ st' ] (st ↦ st')

  is-stuck : State → Set _
  is-stuck st = ∄[ st' ] (st ↦ st')
  
----------------------
  -- 定義 *↦ ，這邊的定義跟 NoRepeat 那邊相反，因為著重的是最後一項要可拆分(st₂ ↦ st₃)
  data _*↦_ : State → State → Set (L.suc ℓ) where
    ◾ : {st : State} → st *↦ st
    _∷_ : {st₁ st₂ st₃ : State} → st₁ *↦ st₂ → st₂ ↦ st₃ → st₁ *↦ st₃

  -- 定義 [n]↦ ，概念跟 *↦ 一樣
  data _[_]↦_ : State → ℕ → State → Set (L.suc ℓ) where
    ◾ : ∀ {st} → st [ 0 ]↦ st
    _∷_ : ∀ {st₁ st₂ st₃ n}
      → st₁ [ n ]↦ st₂
      → st₂ ↦ st₃
      → st₁ [ suc n ]↦ st₃

  -- 確保 *↦ 跟 [n]↦ 的互相轉換
  [n]↦* : ∀ {n st₀ stₙ}
    → st₀ [ n ]↦ stₙ
    → st₀ *↦ stₙ
  [n]↦* {0} {st₀} {.st₀} ◾ = ◾
  [n]↦* {suc n} {st₀} {stₙ} (st₀[n]↦st₂ ∷ st₂↦stₙ)
    = ([n]↦* st₀[n]↦st₂) ∷ st₂↦stₙ

  *↦[n] : ∀ {st₀ stₙ}
    → st₀ *↦ stₙ
    → ∃[ n ] (st₀ [ n ]↦ stₙ)
  *↦[n] {st₀} {.st₀} ◾ = 0 , ◾
  *↦[n] (st₀*↦st₂ ∷ st₂↦stₙ) =  1 + proj₁ (*↦[n] st₀*↦st₂) , (proj₂ (*↦[n] st₀*↦st₂) ∷ st₂↦stₙ)

  -- 另外補上，從 ↦ 抽出 step 的方法
  [n]↦n : {st₀ : State} {stₙ : State} {n : ℕ} → (st₀ [ n ]↦ stₙ) → ℕ
  [n]↦n {n = n} st₀[n]↦stₙ = n
  
  *↦n : {st₀ : State} {stₙ : State} → (st₀ *↦ stₙ) → ℕ
  *↦n st₀*↦stₙ = proj₁ (*↦[n] st₀*↦stₙ)

  -- 定義 is-reachable ，限定在 is-initial
  is-reachable : State → ℕ → State → Set _
  is-reachable st₀ n stₙ = (is-initial st₀) × (st₀ [ n ]↦ stₙ)

  -- is-reachable 縮寫
  _↦_↦_ : State → ℕ → State → Set _
  st₀ ↦ n ↦ stₙ = is-reachable st₀ n stₙ

  -- 確認初始值: st₀ 可抵達 st₀
  initial-is-reachable : ∀ {st} → is-initial st → st ↦ 0 ↦ st
  initial-is-reachable st-initial = st-initial , ◾

  -- 確認 reachable st₀ st 可以拿出 initial st₀
  reachable-proj₁-initial : ∀ {st₀ n st} → st₀ ↦ n ↦ st → is-initial st₀
  reachable-proj₁-initial st₀↦n↦st = proj₁ st₀↦n↦st

  -- 確認 reachable st₀ st 可以拿出 step
  reachable-step : {st₀ : State} {n : ℕ} {st : State} → st₀ ↦ n ↦ st → ℕ
  reachable-step st₀↦↦st = [n]↦n (proj₂ st₀↦↦st)

  -- st₀ [ n ]↦ stₙ
  -- stₙ ≃ (fn : Fin N) → toℕ fn ≡ m
  -- ∀ N → (f : (toℕ State↔FinN .to stₙ)) -- stₙ not the type ℕ
  --  → (∀ n → n ≤ N → f n < N)
  --  → ∃[ m ] ∃[ n ] ( m < n × n ≤ N × f n ≡ f m )
  {-
    pigeonhole-RevMachine : ∀ N → (f : State → ℕ) → (st₀ : State)
           → (∀ n → ∀ st → n ≤ N → st₀ ↦ n ↦ st × f st < N)
           → ∃[ m ] ∃[ n ] ∃[ stₘ ] ∃[ stₙ ] (m < n × n ≤ N × ((st₀ ↦ n ↦ stₙ) × (st₀ ↦ m ↦ stₘ) × (f stₙ ≡ f stₘ) ))
   -}
{-*
  _ : ...
    → State ↔ Fin n 
    → len something > n → ⊥
-} 
{-
  sub0-pigeon : ∀ {N st₀}
    → (State-Fin-N : State ≃ Fin N)
    → ∀ {stₙ n} → n ≤ N → st₀ ↦ n ↦ stₙ
    → ∃[ s ] ∃[ t ] (s < t × t ≤ N × f {N} {State-Fin-N} {st₀} s {_} {_} ≡ f {N} {State-Fin-N} {st₀} t {_} {_})
  sub0-pigeon State-Fin-N {stₙ} {n} n≤N st₀↦↦stₙ = {!!} -- {! pigeonhole ? ?!}

-}

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

  -- step → State → Fin N → ℕ
  Step→State : ∀ st₀
    → ℕ → State
  Step→State stₙ 0 = stₙ
  Step→State stₙ (suc n) with has-next stₙ
  ... | .true because ofʸ (stₙ₊₁ , stₙ→stₙ₊₁) = Step→State stₙ₊₁ n 
  ... | .false because ofⁿ ¬p = stₙ

  Fin→ℕ : ∀ {N}
    → Fin N → ℕ
  Fin→ℕ fn = toℕ fn

  Step→Fin : ∀ {N}
    → State ⤖ Fin N
    → State
    → ℕ → Fin N
  Step→Fin St-Fin st₀ n with Step→State st₀ n
  ... | stₙ with to St-Fin stₙ
  ... | fn = fn

  Step→ℕ : ∀ {N}
    → State ⤖ Fin N
    → State
    → ℕ → ℕ
  Step→ℕ {N} St-Fin st₀ n with Step→State st₀ n
  ... | stₙ with to St-Fin stₙ
  ... | fn with Fin→ℕ fn
  ... | result = result

  FinN<N : ∀ {N : ℕ} (fn : Fin N)
    → (toℕ fn) < N
  FinN<N Fin.zero = s≤s z≤n
  FinN<N (Fin.suc fn) = s≤s (FinN<N fn)
  

  sub1-1 : ∀ {N st₀}
    → (St-Fin : State ⤖ Fin (N))
    → (∀ n → n ≤ N → (Step→ℕ St-Fin st₀ n) < N)
  sub1-1 {N} {st₀} St-Fin n n≤N with (Step→Fin St-Fin st₀ n)
  ... | FinN = FinN<N FinN


  m<N→stₘ≢stₙ : ∀ {st₀ m n}
    → is-initial st₀
    → m < n
    → Step→State st₀ m ≢ Step→State st₀ n
  m<N→stₘ≢stₙ = {!!} -- No Repeat

  stₘ≢stₙ→fm≢fn : ∀ {N stₘ stₙ}
    → (St-Fin : State ⤖ Fin N)
    → stₘ ≢ stₙ
    → to St-Fin stₘ ≢ to St-Fin stₙ
  stₘ≢stₙ→fm≢fn = {!!}

  fm≢fn→tofm≢tofn : ∀ {N fm fn}
    → fm ≢ fn
    → toℕ {N} fm ≢ toℕ {N} fn
  fm≢fn→tofm≢tofn = {!!}


  -- m₁<n₁ → stₘ ≢ stₙ
  -- stₘ ≢ stₙ → fm ≢ fn
  -- fm ≢ fn → tofm ≢ tofn
  
  sub1 : ∀ {N m st₀ stₙ}
    → State ⤖ Fin (N)
    → is-initial st₀
    → m ≡ (N)
    → st₀ ↦ m ↦ stₙ → ⊥

  sub1 {N} {m} {st₀} {stₙ} St-Fin st₀-initial m≡N st₀↦ⁿ↦stₙ with Step→ℕ St-Fin st₀
  ... | f with sub1-1 {N} {st₀} St-Fin
  ... | line2 with pigeonhole (N) (Step→ℕ St-Fin st₀) line2
  ... | m₁ , n₁ , m₁<n₁ , n₁≤N , tofn₁≡tofm₁ with m<N→stₘ≢stₙ {st₀} {m₁} {n₁} st₀-initial m₁<n₁
  ... | stₘ≢stₙ with stₘ≢stₙ→fm≢fn  St-Fin stₘ≢stₙ
  ... | fm≢fn with fm≢fn→tofm≢tofn fm≢fn
  ... | tofm≢tofn = tofm≢tofn (sym tofn₁≡tofm₁)


  sub2 : ∀ {m n}
    → m + 0 ≡ n
    → m ≡ n
  sub2 {m} {n} m+0≡n = trans (sym (+-comm m 0)) m+0≡n 

  sub8 : ∀ {st₀ m stₘ}
    → st₀ ↦ m ↦ stₘ
    → st₀ *↦ stₘ
  sub8 (_ , st₀[m]stₘ) = [n]↦* st₀[m]stₘ

  {-
    st₀  ↦  st₁  ↦  st₂  ↦  st₃  ↦  stₙ₋₁  ↦  stₙ
    0       1       2       3       n-1       n (≡N) ∀ n → n ≤ N
    FinN    FinN    FinN    FinN    FinN      FinN
    g(FinN) g(FinN) g(FinN) g(FinN) g(FinN)   g(FinN)
    f( n ) => st₀ ↦[n] stₙ 轉換成 stₙ， State ⤖ Fin N 轉換 stₙ 為 FinN ，toℕ FinN 轉換成結果
                                                     f n < N
  -}

  cd-1 : ∀ {m} {cd} {N}
    → (m) + (suc cd) ≡ N
    → (suc m) + (cd) ≡ N
  cd-1 {m} {cd} eql =  trans (sym (+-suc m cd)) eql 


  p1 : ∀ {N st₀ m stₘ}
    → (cd : ℕ) → m + cd ≡ N
    → State ⤖ Fin N
    → is-initial st₀
    → st₀ ↦ m ↦ stₘ
    → ∃[ stₙ ] (st₀ *↦ stₙ × is-stuck stₙ)

  p1 {N} {st₀} {m} {stₘ} (suc cd) sum-eql St-Fin st₀-initial st₀↦ᵐstₘ with has-next stₘ
  ... | .true because ofʸ p = p1 {N} {st₀} {suc m} {proj₁ p} cd (cd-1 sum-eql) St-Fin st₀-initial (proj₁ st₀↦ᵐstₘ , (proj₂ st₀↦ᵐstₘ ∷ proj₂ p)) 
  ... | .false because ofⁿ ¬p = stₘ , sub8 st₀↦ᵐstₘ , ¬p

  p1 {N} {st₀} {m} {stₘ} 0 m+0≡N St-Fin st₀-initial st₀↦ᵐstₘ with sub2 m+0≡N
  ... | m≡N with sub1 {N} {m} {st₀} {stₘ} St-Fin st₀-initial m≡N st₀↦ᵐstₘ
  ... | ()


