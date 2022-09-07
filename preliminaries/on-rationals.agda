{-# OPTIONS --allow-unsolved-metas #-}

module preliminaries.on-rationals where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ using ()
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import Agda.Builtin.Unit using (tt)


--- some more constants ---

1/3 = ℤ.+ 1 ℚ./ 3
2/3 = ℤ.+ 2 ℚ./ 3


--- on small rational numbers ---

Positive-½ : ℚ.Positive ½
Positive-½ = tt

0ℚ<½^p : (p : ℕ) → 0ℚ ℚ.< ½ ^ p
0ℚ<½^p ℕ.zero = ℚ.positive⁻¹ tt
0ℚ<½^p (suc p) = begin-strict
  0ℚ             ≡⟨⟩
  ½ ℚ.* 0ℚ       <⟨ ℚ.*-monoʳ-<-pos ½ Positive-½ (0ℚ<½^p p) ⟩
  ½ ℚ.* (½ ^ p)  ∎
  where
  open ℚ.≤-Reasoning

½^sucp+½^sucp≡½^p : (p : ℕ) → ½ ^ (suc p) ℚ.+ ½ ^ (suc p) ≡ ½ ^ p
½^sucp+½^sucp≡½^p zero = refl
½^sucp+½^sucp≡½^p (suc p) =
  begin
  ½ ^ suc (suc p) ℚ.+ ½ ^ suc (suc p)  ≡⟨⟩
  ½ ℚ.* ½ ^ suc p ℚ.+ ½ ℚ.* ½ ^ suc p  ≡˘⟨ ℚ.*-distribˡ-+ ½ (½ ^ suc p) (½ ^ suc p) ⟩
  ½ ℚ.* (½ ^ suc p ℚ.+ ½ ^ suc p)      ≡⟨ cong (½ ℚ.*_) (½^sucp+½^sucp≡½^p p) ⟩
  ½ ^ suc p                            ∎
  where
  open ≡-Reasoning


--- archimedian properties ---

archimedian : (a : ℚ) → Σ ℕ (λ p → (ℤ.+ 2 ℚ./ 1) ^ p ℚ.> a)
archimedian = {!!}

archimedian-ε : (a : ℚ) → ℚ.Positive a → Σ ℕ (λ p → ½ ^ p ℚ.< a)
archimedian-ε = {!!}


--- on triangle inequality ---

differenceOfSums :
  (a b a' b' : ℚ) →
  (a ℚ.+ b) ℚ.- (a' ℚ.+ b') ≡ (a ℚ.- a') ℚ.+ (b ℚ.- b')
differenceOfSums a b a' b' =
  begin-equality
  (a + b) - (a' + b')     ≡⟨ cong ((a + b) ℚ.+_) (ℚ.neg-distrib-+ a' b') ⟩
  (a + b) + (- a' - b')   ≡˘⟨ ℚ.+-assoc (a + b) (- a') (- b') ⟩
  ((a + b) + - a') - b'   ≡⟨ cong (_- b') (ℚ.+-assoc a b (- a')) ⟩
  (a + (b - a')) - b'     ≡⟨ cong (λ x → (a + x) - b') (ℚ.+-comm b (- a')) ⟩
  (a + (- a' + b)) - b'   ≡˘⟨ cong (_- b') (ℚ.+-assoc a (- a') b) ⟩
  ((a - a') + b) - b'     ≡⟨ ℚ.+-assoc (a - a') b (- b') ⟩
  (a - a') + (b - b')     ∎
  where
  open ℚ.≤-Reasoning
  open import Data.Rational
