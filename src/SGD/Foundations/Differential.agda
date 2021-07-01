{-# OPTIONS --without-K --rewriting #-}
module SGD.Foundations.Differential where

open import Function
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import SGD.Foundations.Axioms

δ : (Line → Line) → Line → Inf → Line
δ f x ε = f (x +ᵢ ε)

_′_ : (Line → Line) → Line → Line
f ′ x = approx (δ f x)

taylor : (f : Line → Line) → (x : Line) → (ε : Inf) → f (x +ᵢ ε) ≡ f x + ε *ᵢ (f ′ x)
taylor f x ε = kock-lawvere (δ f x) ε

taylor-approx : (f : Line → Line) → (k : Line) → (x : Line) → (∀ (ε : Inf) → f (x +ᵢ ε) ≡ f x + ε *ᵢ k) → f ′ x ≡ k
taylor-approx f k x prf = approx-unique (δ f x) (f ′ x) k (taylor f x) prf

sum : (f g : Line → Line) → (x : Line) → (f +f g) ′ x ≡ (f ′ x) + (g ′ x)
sum f g x = taylor-approx (f +f g) ((f ′ x) + (g ′ x)) x $ λ (ε , ε-inf) → begin
  f (x + ε) + g (x + ε)
    ≡⟨ cong₂ _+_ (taylor f x (ε , ε-inf)) (taylor g x (ε , ε-inf)) ⟩
  f x + ε * (f ′ x) + (g x + ε * (g ′ x))
    ≡⟨ cong (λ ϕ → f x + ϕ + ε * (g ′ x)) (+-comm (ε * f ′ x) (g x)) ⟩
  f x + g x + ε * f ′ x + ε * g ′ x
    ∎

product : (f g : Line → Line) → (x : Line) → ((f *f g) ′ x) ≡ (f ′ x) * g x + f x * (g ′ x)
product f g x = taylor-approx (f *f g) ((f ′ x) * g x + f x * (g ′ x)) x $ λ (ε , ε-inf) → begin
  f (x + ε) * g (x + ε)
    ≡⟨ cong₂ _*_ (taylor f x (ε , ε-inf)) (taylor g x (ε , ε-inf)) ⟩
  (f x + ε * (f ′ x)) * (g x + ε * (g ′ x))
    ≡⟨⟩
  f x * g x + f x * ε * (g ′ x) + ε * (f ′ x) * g x + ε * (f ′ x) * ε * (g ′ x)
    ≡⟨ cong (λ ϕ →   f x * g x + ϕ + ε * (f ′ x) * ε * (g ′ x)) (+-comm (f x * ε * (g ′ x)) (ε * (f ′ x) * g x)) ⟩
  f x * g x + ε * (f ′ x) * g x + f x * ε * (g ′ x) + ε * (f ′ x) * ε * (g ′ x)
    ≡⟨ cong (λ ϕ →  f x * g x + ε * (f ′ x) * g x + ϕ * (g ′ x) + ε * (f ′ x) * ε * (g ′ x)) (*-comm (f x) ε) ⟩
  f x * g x + ε * (f ′ x) * g x + ε * f x * (g ′ x) + ε * (f ′ x) * ε * (g ′ x)
    ≡⟨ cong (λ ϕ → f x * g x + ε * (f ′ x) * g x + ε * f x * (g ′ x) + ε * ϕ * (g ′ x)) (*-comm (f ′ x) ε) ⟩
  f x * g x + ε * (f ′ x) * (g x) + ε * (f x) * (g ′ x) + ((ε * ε) * (f ′ x) * (g ′ x))
    ≡⟨ cong (λ ϕ →  (f x) * (g x) + ε * (f ′ x) * (g x) + ε * (f x) * (g ′ x) + (ϕ * (f ′ x) * (g ′ x))) ε-inf ⟩
  f x * g x + ε * ((f ′ x) * g x + f x * (g ′ x))
    ∎

chain : (f g : Line → Line) → (x : Line) → ((f ∘′ g) ′ x) ≡ (f ′ (g x)) * (g ′ x)
chain f g x = taylor-approx (f ∘′ g) ((f ′ g x) * (g ′ x)) x $ λ (ε , ε-inf) → begin
  f (g (x + ε))
    ≡⟨ cong f (taylor g x (ε , ε-inf)) ⟩
  f (g x + ε * (g ′ x))
    ≡⟨ taylor f (g x) ((ε * (g ′ x)) , *ᵢ-inf (ε , ε-inf) (g ′ x)) ⟩
  f (g x) + ε * (g ′ x) * (f ′ g x)
    ≡⟨ cong (λ ϕ → f (g x) + ε * ϕ) (*-comm (g ′ x) (f ′ g x)) ⟩
  f (g x) + ε * (f ′ g x) * (g ′ x)
    ∎

id-const : ∀ (x : Line) → id ′ x ≡ 1#
id-const x = taylor-approx id 1# x λ _ → refl
