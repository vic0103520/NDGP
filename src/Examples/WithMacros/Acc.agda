{-# OPTIONS --safe --with-K #-}
-- {-# OPTIONS -v tc.unquote.def:15 #-}
-- {-# OPTIONS -v tc.term.istype:10 #-}
-- {-# OPTIONS -v tc.data.con:20 #-}
-- {-# OPTIONS -v tc.term.expr.top:15 #-}
-- {-# OPTIONS -v tc.term.expr.top.detailed:80 #-}
-- {-# OPTIONS -v tc.check.app:20 #-}
-- {-# OPTIONS -v tc.term.con:50 #-}
-- {-# OPTIONS -v tc.term.app:30 #-}
-- {-# OPTIONS -v tc.term.expr.impl:15 #-}
-- {-# OPTIONS -v test:15 #-}

module Examples.WithMacros.Acc where

open import Prelude hiding (lookupAny)

open import Generics.Description
open import Generics.Recursion
open import Generics.Reflection

open import Generics.RecursionScheme
open import Generics.SimpleContainer
open import Generics.SimpleContainer.Any

data Acc {A : Set ℓ} (R : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  acc : {x : A} → ((y : A) → R y x → Acc R y) → Acc R x

--------
-- Strong induction as the fold operator on Acc

AccD = genDataD Acc
AccC = genDataC AccD (genDataT AccD Acc)

-- private
--   foldAccP : FoldP
--   foldAccP = fold-operator AccC

-- unquoteDecl foldAcc = defineFold foldAccP foldAcc
-- -- foldAcc :
-- --   ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'} {P : A → Set ℓ''}
-- --   → ((x : A) → ((y : A) → R y x → P y) → P x)
-- --   → (x : A) → Acc R x → P x
-- -- foldAcc p x (acc accs) = p x (λ y r → foldAcc p y (accs y r)) 

-- foldAccC = genFoldC foldAccP foldAcc

--------
-- Descending chains in terms of the Any predicate

instance
  AccS : SCᵈ AccD
  AccS = record
    { El  = λ (A , _) → A
    ; pos = (true ∷ tt ∷ []) ∷ []
    ; coe = λ _ → (refl ,ωω λ _ → lift tt) ,ωω lift tt }

private
  AccAnyD : DataD
  AccAnyD = AnyD AccC AccS

unquoteDecl data AccAny constructor c0 c1 = defineByDataD AccAnyD AccAny (c0 ∷ c1 ∷ [])
-- AccAny : {A : Set ℓ} (R : (z z₁ : A) → Set ℓ₁) (P : (z : A) → Set ℓ₂) → Set (ℓ₂ ⊔ ℓ ⊔ ℓ₁)

-- data AccAny {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'}
--   (P : A → Set ℓ'') : {x : A} → Acc R x → Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
--   here  : ∀ {x accs} → P x → AccAny P (acc accs)
--   there : ∀ {x accs y} (r : R y x)
--         → AccAny P (accs y r) → AccAny P (acc accs)

-- data AccAny {ℓ₃ : Level} {ℓ₃ : Level} {ℓ₄ : Level} {A : Set ℓ₃} {R : (z z₁ : A) → Set ℓ₄} (P : (z : A) → Set ℓ₅) : {z : A} (n : Acc R z) → Set (ℓ₅ ⊔ ℓ₃ ⊔ ℓ₄) where
--   c0 : (a : A) {a₁ : (a₂ : A) (a₃ : R a₂ a) → Acc R a₂} (a₂ : P a) →
--      AccAny P (acc a₁)
--   c1 : (a : A) {a₁ : (a₂ : A) (a₃ : R a₂ a) → Acc R a₂} (a₂ : A)
--      (a₃ : R a₂ a) (a₄ : AccAny P (a₁ a₂ a₃)) →
--      AccAny P (acc a₁)

-- AccAnyT = genDataT AccAnyD AccAny
-- AccAnyC = genDataC AccAnyD AccAnyT

-- private
--   lookupAnyAccP : FoldP
--   lookupAnyAccP = lookupAny AccC AccS AccAnyC

-- unquoteDecl lookupAnyAcc = defineFold lookupAnyAccP lookupAnyAcc
-- lookupAnyAcc :
--   ∀ {ℓ'' ℓ ℓ'} {A : Set ℓ} {R : A → A → Set ℓ'} {P : A → Set ℓ''}
--   {x : A} {a : Acc R x} → AccAny P x a → Σ A P
-- lookupAnyAcc (here p   ) = _ , p
-- lookupAnyAcc (there _ i) = lookupAnyAcc i

-- lookupAnyAccC = genFoldC lookupAnyAccP lookupAnyAcc