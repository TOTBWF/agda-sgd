{-# OPTIONS --without-K --rewriting #-}
module SGD.Foundations.Axioms where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Function
open import Level

open import Data.Product
open import Data.Unit using (⊤)
open import Data.Maybe.Base using (just; nothing)

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Structures

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import SGD.Foundations.RingAlgebra


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

-- We postulate each of the ring axioms by hand here so that we can take advantage of REWRITE
postulate
  +-identityˡ : ∀ x → 0# + x ≡ x 
  {-# REWRITE +-identityˡ #-}
  +-identityʳ : ∀ x → x + 0# ≡ x
  {-# REWRITE +-identityʳ #-}
  +-assoc : ∀ x y z → x + (y + z) ≡ x + y + z
  {-# REWRITE +-assoc #-}
  neg-inverseˡ : ∀ x → (- x) + x ≡ 0#
  {-# REWRITE neg-inverseˡ #-}
  neg-inverseʳ : ∀ x → x + (- x) ≡ 0#
  {-# REWRITE neg-inverseʳ #-}
  +-comm : ∀ x y → x + y ≡ y + x

  *-identityˡ : ∀ x → 1# * x ≡ x
  {-# REWRITE *-identityˡ #-}
  *-identityʳ : ∀ x → x * 1# ≡ x 
  {-# REWRITE *-identityʳ #-}
  *-assoc : ∀ x y z → x * (y * z) ≡ x * y * z
  {-# REWRITE *-assoc #-}
  *-comm : ∀ x y → x * y ≡ y * x

  distribˡ : ∀ x y z → x * (y + z) ≡ x * y + x * z
  {-# REWRITE distribˡ #-}
  distribʳ : ∀ x y z → (y + z) * x ≡ y * x + z * x
  {-# REWRITE distribʳ #-}
  zeroˡ : ∀ x → 0# * x ≡ 0#
  {-# REWRITE zeroˡ #-}
  zeroʳ : ∀ x → x * 0# ≡ 0#
  {-# REWRITE zeroʳ #-}

line-is-ring : IsCommutativeRing _≡_ _+_ _*_ -_ 0# 1#
line-is-ring = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = +-assoc
            }
          ; identity = +-identityˡ , +-identityʳ
          }
        ; inverse = neg-inverseˡ , neg-inverseʳ
        ; ⁻¹-cong = cong -_
        }
      ; comm = +-comm
      }
    ; *-isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong = cong₂ _*_
          }
        ; assoc = *-assoc
        }
      ; identity = *-identityˡ , *-identityʳ
      }
    ; distrib = distribˡ , distribʳ
    ; zero = zeroˡ , zeroʳ
    }
  ; *-comm = *-comm
  }

line : CommutativeRing 0ℓ 0ℓ
line = record
  { Carrier = Line
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0#
  ; 1# = 1#
  ; isCommutativeRing = line-is-ring
  }

module line = CommutativeRing line

_+f_ : Op₂ (Line → Line)
f +f g = λ x → f x + g x

_*f_ : Op₂ (Line → Line)
f *f g = λ x → f x * g x

--------------------------------------------------------------------------------
-- Infintesimals

IsInf : Line → Set
IsInf x = (x * x ≡ 0#)

Inf : Set
Inf = Σ[ x ∈ Line ] (x * x ≡ 0#)

0ε : Inf
0ε = 0# , refl

_² : Inf → Inf
(ε , ε-inf) ² = (ε * ε) , cong₂ _*_ ε-inf ε-inf

infixl 7 _*ᵢ_
infixl 6 _+ᵢ_

-- Helpers for operations on infintesimals
_+ᵢ_ : Line → Inf → Line
x +ᵢ (ε , _) = x + ε

_*ᵢ_ : Inf → Line → Line
(ε , _) *ᵢ x = ε * x

*ᵢ-inf : (ε : Inf) → (x : Line) → IsInf (ε *ᵢ x)
*ᵢ-inf (ε , ε-inf) x = begin
  (ε * x) * (ε * x)
    ≡⟨ cong (λ ϕ → ε * ϕ * x) (*-comm x ε) ⟩
  ε * ε * x * x
    ≡⟨ cong (λ ϕ → ϕ * x * x) ε-inf ⟩
  0#
    ∎

-- Restrict a function onto the infintesimals
restrict : (Line → Line) → Inf → Line
restrict f (ε , _) = f ε

--------------------------------------------------------------------------------
-- The Kock-Lawvere Axiom
-- We use the "elementary" form here, as it's a bit simpler to work with.
-- To simplify further, we split the existential up into 3 statements.

postulate
  -- Given a tiny part of a function 'g', we can linearly approximate 'g' with slope 'b'
  approx       : ∀ (g : Inf → Line) → Line
  kock-lawvere : ∀ (g : Inf → Line) → (ε : Inf) → g ε ≡ g 0ε + ε *ᵢ (approx g)
  -- Furthermore, this approximation is unique.
  approx-unique : ∀ (g : Inf → Line) → (b₀ b₁ : Line) → (∀ (ε : Inf) → g ε ≡ g 0ε + ε *ᵢ b₀) → (∀ (ε : Inf) → g ε ≡ g 0ε + ε *ᵢ b₁) → b₀ ≡ b₁

