{-# OPTIONS --allow-unsolved-metas #-}

module preliminaries.on-rationals where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ using ()
open import Data.Rational
open import Data.Rational.Properties
open import Data.Product
open import Data.Sum

open import Relation.Nullary.Decidable

open import Function.Base using (case_of_)

open import Relation.Binary.PropositionalEquality

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring +-*-ring)

open import Agda.Builtin.Unit using (tt)

open ≤-Reasoning


--- some more constants ---

1/3 = ℤ.+ 1 / 3
2/3 = ℤ.+ 2 / 3


--- on small rational numbers ---

Positive-½ : Positive ½
Positive-½ = tt

0ℚ<a^p : (a : ℚ) → (0ℚ < a) → (p : ℕ) → 0ℚ < a ^ p
0ℚ<a^p a 0<a zero = from-yes (0ℚ <? 1ℚ)
0ℚ<a^p a 0<a (suc p) =
  begin-strict
  0ℚ         ≡⟨ sym (*-zeroʳ a) ⟩
  a * 0ℚ     <⟨ *-monoʳ-<-pos a (positive 0<a)  0<a^p ⟩
  a * a ^ p  ∎
  where
  0<a^p = 0ℚ<a^p a 0<a p

0ℚ≤a^p : (a : ℚ) → (0ℚ ≤ a) → (p : ℕ) → 0ℚ ≤ a ^ p
0ℚ≤a^p a 0≤a zero = from-yes (0ℚ ≤? 1ℚ)
0ℚ≤a^p a 0≤a (suc p) =
  begin
  0ℚ         ≡⟨ sym (*-zeroʳ a) ⟩
  a * 0ℚ     ≤⟨  *-monoˡ-≤-nonNeg a (nonNegative 0≤a) 0≤a^p ⟩
  a * a ^ p  ∎
  where
  0≤a^p = 0ℚ≤a^p a 0≤a p

0ℚ<½^p : (p : ℕ) → 0ℚ < ½ ^ p
0ℚ<½^p p = 0ℚ<a^p ½ (from-yes (0ℚ <? ½)) p

½^sucp+½^sucp≡½^p : (p : ℕ) → ½ ^ (suc p) + ½ ^ (suc p) ≡ ½ ^ p
½^sucp+½^sucp≡½^p p =
  begin-equality
  ½ * ½ ^ p + ½ * ½ ^ p  ≡˘⟨ *-distribʳ-+ (½ ^ p) ½ ½  ⟩
  1ℚ * ½ ^ p             ≡⟨ *-identityˡ (½ ^ p) ⟩
  ½ ^ p                  ∎


--- archimedian properties ---

archimedian : (a : ℚ) → Σ ℕ (λ p → (ℤ.+ 2 / 1) ^ p > a)
archimedian = {!!}

archimedian-ε : (a : ℚ) → Positive a → Σ ℕ (λ p → ½ ^ p < a)
archimedian-ε = {!!}


--- in relation to triangle inequality ---

difference-of-sums :
  (a b a' b' : ℚ) →
  (a + b) - (a' + b') ≡ (a - a') + (b - b')
difference-of-sums a b a' b' =
  begin-equality
  (a + b) - (a' + b')     ≡⟨ cong ((a + b) +_) (neg-distrib-+ a' b') ⟩
  (a + b) + (- a' - b')   ≡˘⟨ +-assoc (a + b) (- a') (- b') ⟩
  ((a + b) + - a') - b'   ≡⟨ cong (_- b') (+-assoc a b (- a')) ⟩
  (a + (b - a')) - b'     ≡⟨ cong (λ x → (a + x) - b') (+-comm b (- a')) ⟩
  (a + (- a' + b)) - b'   ≡˘⟨ cong (_- b') (+-assoc a (- a') b) ⟩
  ((a - a') + b) - b'     ≡⟨ +-assoc (a - a') b (- b') ⟩
  (a - a') + (b - b')     ∎

insert-lemma : (a b c : ℚ) → a - c ≡ (a - b) + (b - c)
insert-lemma a b c =
  begin-equality
  a - c                 ≡˘⟨ cong (_- c) (+-identityʳ a) ⟩
  (a + 0ℚ) - c          ≡˘⟨ cong (λ z → (a + z) - c) (+-inverseˡ b) ⟩
  (a + (- b + b)) - c   ≡˘⟨ cong (_- c) (+-assoc a (- b) b) ⟩
  ((a - b) + b) - c     ≡⟨ +-assoc (a - b) b (- c) ⟩
  (a - b) + (b - c)     ∎

triangle-inequality :
  (a b c : ℚ) →
  ∣ a - c ∣ ≤ ∣ a - b ∣ + ∣ b - c ∣
triangle-inequality a b c =
  begin
  ∣ a - c ∣               ≡⟨ cong ∣_∣ (insert-lemma a b c) ⟩
  ∣ (a - b) + (b - c) ∣   ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (a - b) (b - c) ⟩
  ∣ a - b ∣ + ∣ b - c ∣   ∎


--- on intervals ---

_∈[_,_] : ℚ → ℚ → ℚ → Set
b ∈[ a , c ] = a ≤ b × b ≤ c

dist-interval :
  (a c b b' : ℚ) →
  (b ∈[ a , c ]) → (b' ∈[ a , c ]) →
  ∣ b - b' ∣ ≤ c - a
dist-interval a c b b' (a≤b , b≤c) (a≤b' , b'≤c) =
  case ∣p∣≡p∨∣p∣≡-p (b - b') of λ
    { (inj₁ ∣∣≡) →
        begin
        ∣ b - b' ∣  ≡⟨ ∣∣≡ ⟩
        b - b'      ≤⟨ +-mono-≤ b≤c (neg-antimono-≤ a≤b') ⟩
        c - a       ∎
    ; (inj₂ ∣∣≡-) →
        begin
        ∣ b - b' ∣          ≡⟨ ∣∣≡- ⟩
        - (b - b')          ≡⟨ neg-distrib-+ b (- b') ⟩
        (- b) + (- (- b'))  ≡⟨ cong ((- b) +_) (negnegb'≡b' b') ⟩
        (- b) + b'          ≡⟨ +-comm (- b) b' ⟩
        b' - b              ≤⟨ +-mono-≤ b'≤c (neg-antimono-≤ a≤b) ⟩
        c - a               ∎
    }
    where
    -- I can't find this in the stdlib.
    negnegb'≡b' : (b' : ℚ) → - (- b') ≡ b'
    negnegb'≡b' (mkℚ (ℤ.+_ zero) denominator-1 isCoprime) = refl
    negnegb'≡b' (mkℚ +[1+ n ] denominator-1 isCoprime) = refl
    negnegb'≡b' (mkℚ (ℤ.-[1+_] n) denominator-1 isCoprime) = refl
