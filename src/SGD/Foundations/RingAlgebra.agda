{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Ring Algebras
-- NOTE: This should probably be brought into the stdlib at some point
--
module SGD.Foundations.RingAlgebra where

open import Level

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Structures
open import Algebra.Module.Structures

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

private
  variable
    m ℓm r ℓr : Level
    M : Set m

module _ (commutativeRing : CommutativeRing r ℓr) where

  open CommutativeRing commutativeRing using () renaming (Carrier to R)

  record IsAlgebra (_≈ᴹ_ : Rel {m} M ℓm) (_+ᴹ_ : Op₂ M) (_*ᴹ_ : Op₂ M) (-ᴹ_ : Op₁ M) (0ᴹ : M) (1ᴹ : M) (_*ₗ_ : Opₗ R M) (_*ᵣ_ : Opᵣ R M) : Set (ℓm ⊔ m ⊔ r ⊔ ℓr) where
    field
      isModule : IsModule commutativeRing _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
      isRing   : IsRing _≈ᴹ_ _+ᴹ_ _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ

    open IsModule isModule public
    open IsRing isRing public

    field
      *ₗ-assoc : ∀ r x y → (r *ₗ (x *ᴹ y)) ≈ᴹ ((r *ₗ x) *ᴹ y)
      *ᵣ-assoc : ∀ r x y → ((x *ᴹ y) *ᵣ r) ≈ᴹ (x *ᴹ (y *ᵣ r))

record ⟨_⟩-Algebra (R : CommutativeRing r ℓr) m ℓm : Set (suc m ⊔ suc ℓm ⊔ r ⊔ ℓr) where
  open CommutativeRing R renaming (Carrier to Carrierᴿ)

  infixr 8 -ᴹ_
  infixr 7 _*ₗ_
  infixr 7 _*ᵣ_
  infixr 7 _*ᴹ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᴹ_ : Op₂ Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ
    0ᴹ : Carrierᴹ
    1ᴹ : Carrierᴹ
    _*ₗ_ : Opₗ Carrierᴿ Carrierᴹ
    _*ᵣ_ : Opᵣ Carrierᴿ Carrierᴹ
    isAlgebra : IsAlgebra R _≈ᴹ_ _+ᴹ_ _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ _*ₗ_ _*ᵣ_
