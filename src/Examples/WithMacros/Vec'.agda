module Examples.WithMacros.Vec' where

  open import Prelude

  open import Generics.Recursion
  open import Generics.RecursionScheme
  open import Generics.Reflection 
  open import Generics.Telescope
  
  open import Utils.Reflection.Tactic using (getTelescopeT; evalTC; evalT)
  open import Utils.Reflection.Core

  open import Agda.Builtin.Nat
  
  data Vec (A : Set) : ℕ → Set where
    [] : Vec A 0
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

  VecC = genDataC VecD (genDataT VecD Vec)
    where VecD = genDataD Vec
      
  unquoteDecl indVec = defineInd (ind-operator VecC) indVec

  indVec-tel : Telescope
  indVec-tel = fst $ getTelescopeT indVec

  indVec-tel' : Telescope
  indVec-tel' = correctVsOfTelT indVec-tel
  
  -- {ℓ : Level} {p : Set} (P : {a : ℕ} → Vec p a → Set ℓ) →
  -- P [] →
  -- ((a : ℕ) (a₁ : p) (ns : Vec p a) → P ns → P (a₁ ∷ ns)) →
  -- {a : ℕ} (n : Vec p a) → P n

  -- {ℓ : Level} {p : Set} (P : {a : ℕ} → Vec p a → Set ℓ) →
  -- P [] →
  -- ({a : ℕ} (a₁ : p) (ns : Vec p a) → P ns → P (a₁ ∷ ns)) →
  -- {a : ℕ} (n : Vec p a) → P n