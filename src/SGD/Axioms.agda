{-# OPTIONS --without-K #-}
module SGD.Axioms where

open import Function
open import Data.Product

open import Algebra.Bundles
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- We start by postulating the existence of some abstract commutative ring
-- to act as our notion of line
postulate
  Line : Set
  _+_ : Line → Line → Line
  _*_ : Line → Line → Line
  -_ : Line → Line
  0# : Line
  1# : Line

infixl 7 _*_
infixl 6 _+_

postulate
  line-is-ring : IsCommutativeRing _≡_ _+_ _*_ -_ 0# 1# 

--------------------------------------------------------------------------------
-- The Kock-Lawvere Axiom
Inf : Set
Inf = Σ[ x ∈ Line ] (x * x ≡ 0#)

α : Line × Line → (Inf → Line)
α (a , b) (d , _) = a + (d * b)

postulate
  α⁻¹ : (Inf → Line) → (Line × Line)
  α-isoˡ : α⁻¹ ∘ α ≡ id 
  α-isoʳ : α ∘ α⁻¹ ≡ id 
