{-# OPTIONS --safe --without-K #-}

open import Prelude

module Generics.Reflection.Telescope where
open import Utils.Reflection
open import Utils.Error as Err

open import Agda.Builtin.Nat using (Nat; _-_)
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Tree.AVL.Map (<-strictTotalOrder) as M hiding (foldr)
import Data.Maybe using (_>>=_)
open import Generics.Telescope

import Data.List using (_++_)

-- Frequently used terms
private
  variable
    T U : Tel ℓ
  
  pattern _`∷_ t u = con₂ (quote Tel._∷_) t (vLam u)
  pattern `[]      = con₀ (quote Tel.[])

-- extend the context in a TC computation 
exCxtTel : {A : Set ℓ′}
  → (T : Tel ℓ) → (⟦ T ⟧ᵗ → TC A) → TC A
exCxtTel [] f      = f tt
exCxtTel (A ∷ T) f = do
  s ← getAbsNameω T
  exCxtT s visible-relevant-ω A λ _ x → exCxtTel (T x) (curry f x)
exCxtTel (T ++ U) f = exCxtTel T λ ⟦T⟧ →
  exCxtTel (U ⟦T⟧) λ x → curry f ⟦T⟧ x

exCxtℓs : {A : Set ℓ}
  → (#levels : ℕ) → (Level ^ #levels → TC A) → TC A
exCxtℓs zero    c = c tt
exCxtℓs (suc n) c = exCxtT "ℓ" hidden-relevant-ω Level λ _ ℓ →
    exCxtℓs n (curry c ℓ)

-- ℕ is the length of (T : Tel ℓ)
-- this may fail if `Tel` is not built by λ by pattern matching lambdas.
fromTel : {ℓ : Level}
  → (tel : Tel ℓ) → TelInfo Visibility tel → TC Telescope
fromTel []      _ = return []
fromTel (A ∷ T) (v ∷ U) = do
  s ← getAbsNameω T
  exCxtT s (arg-info v (modality relevant quantity-ω)) A λ `A x → do
    Γ ← fromTel (T x) (U x)
    return $ (s , arg (arg-info v (modality relevant quantity-ω)) `A) ∷ Γ
fromTel (T ++ U) (V ++ W) = do
  `Γ ← fromTel T V
  exCxtTel T λ x → do
    `Δ ← fromTel (U x) (W x)
    return (`Γ <> `Δ)

fromTel' : {ℓ : Level} → (tel : Tel ℓ) → TC Telescope
fromTel' [] = return []
fromTel' (A ∷ T) = do
  s ← getAbsNameω T
  exCxtT s (arg-info visible (modality relevant quantity-ω)) A λ `A x → do
    Γ ← fromTel' (T x)
    return $ (s , arg (arg-info visible (modality relevant quantity-ω)) `A) ∷ Γ
fromTel' (T ++ U) = do
  `Γ ← fromTel' T
  exCxtTel T λ x → do
    `Δ ← fromTel' (U x)
    return (`Γ <> `Δ)

fromTel! : {ℓ : Level}
  → (tel : Tel ℓ) → TelInfo Visibility tel → TC Telescope
fromTel! T V = withNormalisation true $ fromTel T V

to`Tel : Telescope → Term
to`Tel = foldr `[] λ where
  (s , arg _ `A) `T →  `A `∷ abs s `T

fromTelInfo : ∀ {ℓ} → {tel : Tel ℓ} → TelInfo String tel → TC (List String)
fromTelInfo [] = return []
fromTelInfo {tel = A ∷ T} (s ∷ N) = do
  exCxtT s (visible-relevant-ω) A λ `A x → do
    ss ← fromTelInfo (N x)
    return (s ∷ ss)
fromTelInfo {tel = T ++ U} (S ++ S') = do
  ss ← fromTelInfo S
  exCxtTel T λ t → do
    ts ← fromTelInfo (S' t)
    return (ss <> ts)

macro
  genTel : Telescope → Tactic
  genTel Γ hole = do
    `ℓ ← newMeta `Level
    checkedHole ← checkType hole (def₁ (quote Tel) `ℓ)
    unify checkedHole (to`Tel Γ)

-- Check if the given telescope is a prefix of a telescope up to arg-info 
-- and return the telescope with the correct visibility
-- `T ⊆ᵗ? Γ` returns
--   1. a telescope corresponding to T (with `arg-info` copied from Γ) and
--   2. the telescope of Γ without T
_⊆ᵗ?_ : Tel ℓ → Telescope → TC (Telescope × Telescope)
[]      ⊆ᵗ? Γ  = return ([] , Γ)
(A ∷ T) ⊆ᵗ? [] = do
  `A ← quoteTC A
  typeError $ 
    strErr "An extra argument of type" ∷ termErr `A ∷ strErr " to apply" ∷ []
(A ∷ T) ⊆ᵗ? ((s , arg i@(arg-info v m) `B) ∷ Γ) = do
  `A ← quoteTC! A
  unify `A `B <|> (typeError $ termErr `A ∷ strErr " ≠ " ∷ termErr `B ∷ [])
  exCxtT s i A λ _ x → bimap ((s , arg i `B) ∷_) id <$> T x ⊆ᵗ? Γ
(T ++ U) ⊆ᵗ? Γ = do
  (vs , Γ) ← T ⊆ᵗ? Γ
  exCxtTel T λ t → do
    (vs′ , Γ) ← U t ⊆ᵗ? Γ
    return (vs <> vs′ , Γ)

------------------------------------------------------------------------
-- Each constructor `c : (x₁ : A₁) → (x₂ : A₂ x₁) → ⋯ → T`
-- can be represented as a pattern on the LHS `c x₁ x₂ ⋯ xₙ` or as a term on the RHS
-- They can be also uncurried described by ⟦ ConD ⟧. Thus, there are 4 types of constructor representations. 
Vars : Set
Vars = (Term × Pattern) × (Args Term × Args Pattern)

cxtToVars : (from : ℕ) (base : Term × Pattern) (Γ : Telescope)
  → Vars
cxtToVars from base = snd ∘ foldr emptyVar λ where
      (_ , arg i _) (n , (t , p) , (targs , pargs)) →
        suc n , ((var₀ n `, t) , (var n `, p)) , (arg i (var₀ n) ∷ targs) , (arg i (var n) ∷ pargs)
  where emptyVar = from , base , [] , []

cxtToVarPatt : Telescope → Pattern
cxtToVarPatt Γ = let (_ , p) , _ = cxtToVars 0 (`tt , `tt) Γ in p

------------------------------------------------------------------------
-- 

telToVars : (from : ℕ) (base : Term × Pattern)
  → (T : Tel ℓ) (Γ : Telescope) → TC Vars
telToVars from base T Γ = snd <$> go from base T Γ 
  where 
    go : (from : ℕ) (base : Term × Pattern)
      → (T : Tel ℓ) (Γ : Telescope)
      → TC $ ℕ × (Term × Pattern) × (Args Term × Args Pattern)
    go from base []       _       = return (from , base , [] , [])
    go from base (A ∷ T)  []      = typeError
      $ strErr "The length of Tel is different from the length of Telescope" ∷ []
    go from base (A ∷ T)  ((s , arg i B) ∷ Γ) = do
      `A ← quoteTC! A
      exCxtT s i A λ _ x → do
        n , (t , p) , (targs , pargs) ← go from base (T x) Γ
        return $ suc n , ((var₀ n `, t) , (var n `, p)) , arg i (var₀ n) ∷ targs , arg i (var n) ∷ pargs
    go from base (T ++ U) Γ = do
      n ← length <$> fromTel T (constTelInfo visible)
      let (Γ , Δ) = splitAt n Γ
      n , (Δt , Δp) , Δts , Δps ← exCxtTel T λ t → go from base (U t) Δ
      m , (Γt , Γp) , Γts , Γps ← go n base T Γ 
      return $ m , ((Γt `, Δt) , (Γp `, Δp)) , (Γts <> Δts , Γps <> Δps)

-- psToArgs : Telescope → TC (Args Term)
-- psToArgs tel = do
--   dprint (strErr ("psToArgs " <> show tel <> ":\n") ∷ [])
--   ⦇ Prelude.map (⦇ {!   !} ⦈) ⦇ tel ⦈ ⦈
--   where
    
--     help : Arg Term → (Term → Arg Term)
--     help (arg (arg-info visible m) A) = vArg
--     help (arg (arg-info hidden m) A) = hArg
--     help (arg (arg-info instance′ m) A) = iArg
  
psToArgs' : Telescope → Args Term → TC (Args Term)
psToArgs' vs ns = ⦇ (zipWith (λ (s , `arg) n → changeVs n `arg) vs ns) ⦈
  where
    changeVs : Arg Term → Arg Term → Arg Term
    changeVs (arg _ A) (arg (arg-info visible m) _) = vArg A
    changeVs (arg _ A) (arg (arg-info hidden m) _) = hArg A
    changeVs (arg _ A) (arg (arg-info instance′ m) _) = iArg A

-- Translate the semantics of an object-level telescope to a context
idxToArgs : ⟦ T ⟧ᵗ → TC (Args Term)
idxToArgs {T = []}     tt      = ⦇ [] ⦈
idxToArgs {T = _ ∷ _}  (A , Γ) = ⦇ ⦇ vArg (quoteTC A) ⦈ ∷ (idxToArgs Γ) ⦈
idxToArgs {T = _ ++ _} (T , U) = ⦇ (idxToArgs T) <> (idxToArgs U) ⦈

-- ... and back
argsToIdx : Args Term → Term
argsToIdx []       = `tt
argsToIdx (x ∷ xs) = (unArg x) `, argsToIdx xs

-- todo
-- psToArgs - what's the difference between "quoteTC" and "quoteTerm"
-- The fully applied datatype 
typeOfData : Name → (ps : ⟦ U ⟧ᵗ) (vs : Telescope) (is : ⟦ T ⟧ᵗ) → TC Type 
typeOfData d ps vs is = do 
  ps' ← idxToArgs ps
  is' ← idxToArgs is
  ps+is' ← psToArgs' vs (ps' Data.List.++ is')
  return $ def d $ filter isVisible ps+is'
  
module _ where
  argType = Arg Type

  changeVsOfArg : argType → Visibility → argType
  changeVsOfArg (arg (arg-info v m) t) v' = arg (arg-info v' m) t

  changeVsOfArgInfo : ArgInfo → Visibility → ArgInfo
  changeVsOfArgInfo (arg-info _ ty) v = arg-info v ty
                  
  take' : ℕ → Map Visibility → Maybe (Map Visibility)
  take' n m = drop' (size m - n) m
    where
      drop' : ℕ → Map Visibility → Maybe (Map Visibility)
      drop' zero m = just m
      drop' (suc n) m = initLast m Data.Maybe.>>= λ (m' , _) → drop' n m'

  mutual
    -- Hidden args should be passed
    -- Position don't change?
    correctVsOfArgs : List argType → Map Visibility → (pos : Nat) → TC (Map Visibility)
    correctVsOfArgs [] m pos = return m
    correctVsOfArgs (arg (arg-info visible mod) ty ∷ args) m pos = do (_ , m') ← correctVsOfTerm ty m pos
                                                                      correctVsOfArgs args m' pos
    correctVsOfArgs (arg (arg-info v mod) ty ∷ args) m pos = correctVsOfArgs args m pos
                                              
    correctVsOfTerm : Term → Map Visibility → (pos : Nat) → TC (Term × Map Visibility)
    -- top level
    correctVsOfTerm (var n []) m pos with pos Agda.Builtin.Nat.< n + 1 | M.lookup m (pos - n - 1)
    -- accessing parameter won't change cons's signature
    ... | true  | _            = do 
      -- dprint (strErr (show pos <> " : accessing parameter\n") ∷ [])
      return $ var n [] , m
    ... | false | just visible = do 
      -- dprint (strErr (show pos <> " " <> show (pos - n - 1) <> "\n") ∷ [])
      return $ var n [] , M.insert (pos - n - 1) hidden m
    ... | _     | otherwise    = return $ var n [] , m
    correctVsOfTerm (var n args) m pos = return $ var n args , m
    correctVsOfTerm (def f args) m pos = do
      f' ← getDefinition f
      -- dprint (strErr (show f <> ": " <> show f') ∷ [])
      case f' of 
        λ { (data-type _ _)   → do 
              -- dprint (strErr ("datatype: " <> show f <> ", pos: " <> show pos <> "\n") ∷ [])
              m' ← correctVsOfArgs args m pos
              -- dprint (strErr ("end") ∷ [])
              return $ def f args , m'
          ; (record-type _ _) → do m' ← correctVsOfArgs args m pos
                                   return $ def f args , m'
          -- ?
          ; (data-cons _)     → do m' ← correctVsOfArgs args m pos
                                   return $ def f args , m'
          ; axiom             → do 
              -- dprint (strErr ("axiom: " <> show f <> ", pos: " <> show pos <> "\n") ∷ [])
              m' ← correctVsOfArgs args m pos
              -- dprint (strErr ("end") ∷ [])
              return $ def f args , m'
          -- ?
          ; prim-fun          → return $ def f args , m
          ; _                 → return $ def f args , m}
    correctVsOfTerm (con c args) m pos = do 
      -- dprint (strErr ("con: " <> show c) ∷ [])
      m' ← correctVsOfArgs args m pos
      return $ con c args , m'
    correctVsOfTerm (pi (arg i A) (abs s B)) m pos = do (B' , m') ← correctVsOfTerm B (M.insert pos visible m) (suc pos)
                                                        let i' = case (M.lookup m' pos) of 
                                                                  λ { (just v) → changeVsOfArgInfo i v
                                                                    ; nothing  → i
                                                                    }
                                                        --  dprint [ strErr ("pos: " <+> show pos <+> " size of m: " <+> show (size m')) ]
                                                        case take' pos m' of
                                                          λ { nothing   → typeError [ strErr "correctVsOfTerm" ]
                                                              -- just correct visibility of top level parameters, so discard A'
                                                            ; (just m') → do (A' , m'') ← correctVsOfTerm A m' pos
                                                                             return $ pi (arg i' A) (abs s B') , m''
                                                            }
    correctVsOfTerm t m pos = return $ t , m -- Levels are prepended as hidden parameters,
                                             -- so we don't have to process sorts.
                                             -- Other cases won't appear in type signature.
    -- examples?
    -- correctVsOfTerm (Reflection.meta x x₁) m pos = {!   !}

  correctVsOfArg : argType → Map Visibility → (pos : Nat) → TC (argType × Map Visibility)
  correctVsOfArg (arg i ty) m pos = do (ty' , m') ← correctVsOfTerm ty m pos
                                       return $ (arg i ty' , m')

  correctVsOfTel' : (tel : Telescope) → Map Visibility → (pos : Nat) → TC (Telescope × Map Visibility)
  correctVsOfTel' [] m pos = return $ [] , m
  correctVsOfTel' ((s , `arg) ∷ tel) m pos = do (tel' , m')   ← correctVsOfTel' tel (M.insert pos (getVisibility `arg) m) (suc pos)
                                                let `arg' = case (M.lookup m' pos) of 
                                                              λ { (just v) → changeVsOfArg `arg v
                                                                ; nothing  → `arg
                                                                }
                                                case take' pos m' of
                                                  λ { nothing → typeError [ strErr "correctTel" ]
                                                    ; (just m') → do (`arg'' , m'') ← correctVsOfArg `arg' m' pos
                                                                     return $ (s , `arg'') ∷ tel' , m''
                                                    }


  correctVsOfTel : Telescope → TC Telescope
  correctVsOfTel t = fmap fst $ correctVsOfTel' t M.empty zero

macro
  correctVsOfTelT : Telescope → Tactic
  correctVsOfTelT tel = evalTC $ correctVsOfTel tel