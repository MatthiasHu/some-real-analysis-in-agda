module preliminaries.convex-combination where

open import Data.Rational
open import Data.Rational.Properties

open import Relation.Binary.PropositionalEquality

open import preliminaries.on-rationals


module ConvexCombination
  (c d : ℚ)
  (c<d : c < d)
  where

  open ≤-Reasoning

  convex-comb : ℚ → ℚ
  convex-comb t = c + t * (d - c)

  convex-comb-0 : convex-comb 0ℚ ≡ c
  convex-comb-0 =
    begin-equality
    c + 0ℚ * (d - c)   ≡⟨ cong (c +_) (*-zeroˡ (d - c)) ⟩
    c + 0ℚ             ≡⟨ +-identityʳ c ⟩
    c                  ∎

  convex-comb-1 : convex-comb 1ℚ ≡ d
  convex-comb-1 =
    begin-equality
    c + 1ℚ * (d - c)  ≡⟨ cong (c +_) (*-identityˡ (d - c)) ⟩
    c + (d - c)       ≡⟨ add-difference-lemma c d ⟩
    d                 ∎

  d-c-Positive : Positive (d - c)
  d-c-Positive = positive
    (begin-strict
    0ℚ       ≡˘⟨ +-inverseʳ c ⟩
    c - c    <⟨ +-monoˡ-< (- c) c<d ⟩
    d - c    ∎)

  convex-comb-mono :
    (t t' : ℚ) →
    t < t' →
    convex-comb t < convex-comb t'
  convex-comb-mono t t' t<t' = +-monoʳ-< c
    (begin-strict
    t * (d - c)    <⟨ *-monoˡ-<-pos (d - c) d-c-Positive t<t' ⟩
    t' * (d - c)   ∎
    )

  convex-comb-mono-0 : (t : ℚ) → (0ℚ < t) → c < convex-comb t
  convex-comb-mono-0 t 0<t =
    begin-strict
    c               ≡˘⟨ convex-comb-0 ⟩
    convex-comb 0ℚ  <⟨ convex-comb-mono 0ℚ t 0<t  ⟩
    convex-comb t   ∎

  convex-comb-mono-1 : (t : ℚ) → (t < 1ℚ) → convex-comb t < d
  convex-comb-mono-1 t t<1 =
    begin-strict
    convex-comb t   <⟨ convex-comb-mono t 1ℚ t<1  ⟩
    convex-comb 1ℚ  ≡⟨ convex-comb-1 ⟩
    d
    ∎

  convex-comb-diff :
    (t' t : ℚ) →
    convex-comb t' - convex-comb t ≡ (t' - t) * (d - c)
  convex-comb-diff t' t =
    begin-equality
    (c + t' *d-c) - (c + t *d-c)     ≡⟨ difference-of-sums c (t' *d-c) c (t *d-c) ⟩
    ((c - c) + (t' *d-c - t *d-c) )  ≡⟨ cong (_+ (t' *d-c - t *d-c)) (+-inverseʳ c) ⟩
    (0ℚ + (t' *d-c - t *d-c) )       ≡⟨ cong (0ℚ +_) (cong (t' *d-c +_) (neg-distribˡ-* t (d - c))) ⟩
    0ℚ + (t' *d-c + (- t) *d-c)      ≡˘⟨ cong (0ℚ +_) ( *-distribʳ-+ (d - c) t' (- t)) ⟩
    0ℚ + (t' - t) *d-c               ≡⟨ +-identityˡ ((t' - t) * (d - c)) ⟩
    (t' - t) *d-c                    ∎
    where
    _*d-c = _* (d - c)

  convex-comb-diff-0 :
    (t : ℚ) →
    convex-comb t - c ≡ t * (d - c)
  convex-comb-diff-0 t =
    begin-equality
    (convex-comb t - c)               ≡˘⟨ cong (λ z → convex-comb t - z) convex-comb-0 ⟩
    (convex-comb t - convex-comb 0ℚ)  ≡⟨ convex-comb-diff t 0ℚ ⟩
    ((t + 0ℚ) * (d - c))              ≡⟨ cong (_* (d - c)) (+-identityʳ t) ⟩
    (t * (d - c))                     ∎

  convex-comb-diff-1 :
    (t : ℚ) →
    d - convex-comb t ≡ (1ℚ - t) * (d - c)
  convex-comb-diff-1 t =
    begin-equality
    (d - convex-comb t)               ≡˘⟨ cong (_- convex-comb t) convex-comb-1 ⟩
    (convex-comb 1ℚ - convex-comb t)  ≡⟨ convex-comb-diff 1ℚ t ⟩
    ((1ℚ - t) * (d - c))              ∎
