import Level as L
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import RevMachine
open import Function.Inverse using (_↔_)
open import Data.Fin using ( Fin ; toℕ )
open import Relation.Nullary

module RevNoRepeat1022 {ℓ} (M : RevMachine {ℓ}) where
  open RevMachine.RevMachine M
  
  is-initial : State → Set _
  is-initial st = ∄[ st' ] (st' ↦ st)
  
  is-not-stuck : State → Set _
  is-not-stuck st = ∃[ st' ] (st ↦ st')
  
  is-stuck : State → Set _
  is-stuck st = ∄[ st' ] (st ↦ st')

  -- 驗證: 如果針對可抵達的 st ↦ st' ，找到一個矛盾，則可以證明 st 是 stuck
  not-stuck→⊥→stuck : ∀ {st} → (is-not-stuck st → ⊥) → is-stuck st
  not-stuck→⊥→stuck st-not-stuck = st-not-stuck

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
  [n]↦n {n = n} st₀*↦stₙ = n
  
  *↦n : {st₀ : State} {stₙ : State} → (st₀ *↦ stₙ) → ℕ
  *↦n st₀*↦stₙ = proj₁ (*↦[n] st₀*↦stₙ)

  [n]→*→[n] : ∀ {n st₀ stₙ}
    → (st₀[n]↦stₙ : st₀ [ n ]↦ stₙ) → 1 ≡ 1
--    → proj₂ (*↦[n] ([n]↦* st₀[n]↦stₙ)) ≡ st₀[n]↦stₙ
  --  → proj₂ (*↦[n] ([n]↦* (st₀[n]↦stₙ))) ≡ st₀[n]↦stₙ
  [n]→*→[n] st₀[n]↦stₙ = {!!} -- st₀[n]↦stₙ with [n]↦* st₀[n]↦stₙ
--  ... | st₀*↦stₙ = {!!}


  -- 定義 is-reachable ，限定在 is-initial
  is-reachable : State → State → Set _
  is-reachable st₀ st = (is-initial st₀) × (st₀ *↦ st)

  -- is-reachable 縮寫
  _↦↦_ : State → State → Set _
  st₀ ↦↦ st = (is-initial st₀) × (st₀ *↦ st)

  tmp : ∀ {st₀ st} → is-initial st₀ → st₀ *↦ st → is-reachable st₀ st
  tmp a b = a , b

  -- 確認初始值: st₀ 可抵達 st₀
  initial-is-reachable : ∀ {st} → is-initial st → st ↦↦ st
  initial-is-reachable st-initial = st-initial , ◾

  -- 確認 reachable st₀ st 可以拿出 initial st₀
  reachable-proj₁-initial : ∀ {st₀ st} → st₀ ↦↦ st → is-initial st₀
  reachable-proj₁-initial st₀↦↦st = proj₁ st₀↦↦st

  -- 確認 reachable st₀ st 可以拿出 step
  reachable-step : {st₀ : State} {st : State} → st₀ ↦↦ st → ℕ
  reachable-step st₀↦↦st = *↦n (proj₂ st₀↦↦st)

  -- 鴿籠原理，在 Pigeonhole.agda 有證明
  postulate
    pigeonhole : ∀ N → (f : ℕ → ℕ)
           → (∀ n → n ≤ N → f n < N)
           → ∃[ m ] ∃[ n ] (m < n × n ≤ N × f n ≡ f m)

  

{-*
  _ : ...
    → State ↔ Fin n 
    → len something > n → ⊥
-}


  sub1 : ∀ {N st₀}
    → State ↔ Fin N
    → ∀ {stₙ} → (st₀↦↦stₙ : st₀ ↦↦ stₙ) → reachable-step st₀↦↦stₙ < N
  sub1 {N} {st₀} State↔Fin-N {stₙ} st₀↦↦stₙ = {!!}

  sub2 : ∀ {n st₀ stₙ}
    → (st₀-initial : is-initial st₀) → (st₀[n]↦stₙ : st₀ [ n ]↦ stₙ)
    → reachable-step (st₀-initial , ([n]↦* st₀[n]↦stₙ)) ≡ n
  sub2 st₀-initial st₀[n]↦stₙ = {!!}

  trichotomy₁ : ∀{m n : ℕ} → m < n → ¬ m ≡ n
  trichotomy₁ {m} {n} m<n = {!!}
  -- trichotomy₁ (suc m) .(suc _) (s<s _m<n) refl = <-irreflexive m _m<n

  

  -- Fin n 對應到的是0, 1, 2, ..., n-1
  sub3 : ∀ {N st₀}
    → State ↔ Fin N
    → is-initial st₀
    → ∃[ stₙ ] (st₀ [ N ]↦ stₙ) → ⊥


  sub3 {N} {st₀} State↔Fin-N st₀-initial (stₙ , st₀[N]↦stₙ) with [n]↦* st₀[N]↦stₙ
  ... | st₀*↦stₙ with (st₀-initial , st₀*↦stₙ)
  ... | st₀↦↦stₙ with sub1 State↔Fin-N st₀↦↦stₙ
  ... | step<N = (trichotomy₁ step<N) {!sub2 ? ?!} -- {! (sub2 st₀-initial st₀[N]↦stₙ)!}

  -- = _ , (λ st₀[n]↦stₙ → {!!})

  
{-
  st-reachable-is-finite : {n} (st₀ : State) → is-initial st₀
    → ∀ {st m} → (st₀[m]↦st : st₀ [ m ])↦ st → reachableNo {st₀} {st} {m} {st₀-initial} (st₀[m]↦st) < n
-}

{-
  Finite : ∀ {N st₀} → (st₀-initial : is-initial st₀)
    → ∀ {st} → ∃[ m ] ((is-reachable st₀ st) × (reachableNo {st₀} {st} {m} {st₀-initial} (st₀ [ m ]↦ st) < N ))
    → ∃[ stₙ ] ( is-stuck stₙ)
  Finite {n} {st₀} st₀-initial {st} = ?
-}


--  Finite n {st} (st₀ , st₀-is-initial , st₀*↦st) No-st<n = {!stₙ!} , (λ stₙ₁ → {!!})
  -- stₙ 是 st₀ ↦[n] 的結果
  -- 證明 st₀ ↦[n] stₙ 則 No stₙ = No st₀ + n
  -- 對stₙ₁來說 stₙ₁ is reachable → reachableNo {stₙ₁} st-reachable < n
  -- 首先確定 st₀~stₙ₁ 之間的所有state都<n
  -- use pigeonhole principle, 會存在一個 stₘ s.t. stₙ ≡ stₘ
  -- 他會跟 NoRepeat 衝突，帶入 ?3
  
