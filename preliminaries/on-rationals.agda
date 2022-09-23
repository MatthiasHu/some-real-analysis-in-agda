{-# OPTIONS --allow-unsolved-metas #-}

module preliminaries.on-rationals where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ using ()
import Data.Integer.Properties as ℤ
open import Data.Rational
open import Data.Rational.Properties
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Function.Base using (case_of_; _∘_)

open import Relation.Binary.PropositionalEquality

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring +-*-ring)

open import Agda.Builtin.Unit using (tt)

open ≤-Reasoning

open import Erased.With-K


--- some more constants ---

1/2 = ½
1/3 = ℤ.+ 1 / 3
2/3 = ℤ.+ 2 / 3
1/4 = ℤ.+ 1 / 4
3/4 = ℤ.+ 3 / 4
2ℚ = ℤ.+ 2 / 1



--- on negation

neg-neg : (a : ℚ) → - (- a) ≡ a
neg-neg (mkℚ (ℤ.+_ zero) denominator-1 isCoprime) = refl
neg-neg (mkℚ +[1+ n ] denominator-1 isCoprime) = refl
neg-neg (mkℚ (ℤ.-[1+_] n) denominator-1 isCoprime) = refl

neg-diff : (a b : ℚ) → - (a - b) ≡ b - a
neg-diff a b =
  begin-equality
        - (a - b)          ≡⟨ neg-distrib-+ a (- b) ⟩
        (- a) + (- (- b))  ≡⟨ cong ((- a) +_) (neg-neg b) ⟩
        (- a) + b          ≡⟨ +-comm (- a) b ⟩
        b - a              ∎


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

½^p-½^sucp≡½^sucp : (p : ℕ) → ½ ^ p - ½ ^ (suc p) ≡ ½ ^ (suc p)
½^p-½^sucp≡½^sucp p =
  begin-equality
  ½ ^ p - ½ ^ suc p        ≡⟨ cong₂ _+_ (sym (*-identityˡ (½ ^ p))) (neg-distribˡ-* ½ (½ ^ p)) ⟩
  1ℚ * ½ ^ p + -½ * ½ ^ p  ≡˘⟨ *-distribʳ-+ (½ ^ p) 1ℚ -½ ⟩
  (1ℚ + -½) * ½ ^ p        ≡⟨ cong (_* (½ ^ p)) (refl {x = ½}) ⟩
  ½ ^ suc p
  ∎

½^sucp<½^p : (p : ℕ) → ½ ^ suc p < ½ ^ p
½^sucp<½^p p =
  begin-strict
  ½ ^ suc p              ≡˘⟨ +-identityˡ _ ⟩
  0ℚ        + ½ ^ suc p  <⟨ +-monoˡ-< (½ ^ suc p) (0ℚ<½^p (suc p)) ⟩
  ½ ^ suc p + ½ ^ suc p  ≡⟨ ½^sucp+½^sucp≡½^p p ⟩
  ½ ^ p                  ∎


--- archimedean properties ---

archimedean : (a : ℚ) → Σ ℕ (λ p → Erased (a < 2ℚ ^ p))
archimedean (mkℚ (ℤ.+_ n) d-1 _) = n , [ {!!} ]
archimedean (mkℚ (ℤ.-[1+_] n) d-1 _) = zero , [ *<* ℤ.-<+ ]

import Relation.Nullary.Decidable as Dec

stable-¬ : {ℓ : _} {A : Set ℓ} → @0 ¬ A → ¬ A
stable-¬ ¬a a with () ← Erased.With-K.[ ¬a a ]

pos⇒≢0 : ∀ p → @0 Positive p → False (ℤ.∣ ↥ p ∣ ℕ.≟ 0)
pos⇒≢0 p p>0 = Dec.fromWitnessFalse
                 (stable-¬ ((≢-sym (ℤ.<⇒≢ (ℤ.positive⁻¹ p>0))) ∘ ℤ.∣n∣≡0⇒n≡0))

archimedean-ε : (a : ℚ) → @0 Positive a → Σ ℕ (λ p → Erased (½ ^ p < a))
archimedean-ε a a-pos =
  let (p , _) = archimedean ((1/ a) {n≢0 = pos⇒≢0 a a-pos}) -- pos⇒≢0
  in p , [ {!!} ]


--- on absolute value ---

≤∣-∣ : (a : ℚ) → a ≤ ∣ a ∣
≤∣-∣ a = case ∣p∣≡p∨∣p∣≡-p a of λ
  { (inj₁ ∣a∣≡a) → ≤-reflexive (sym ∣a∣≡a)
  ; (inj₂ ∣a∣≡-a) →
      begin
      a        ≡⟨ sym (neg-neg a) ⟩
      - (- a)  ≡˘⟨ cong -_ ∣a∣≡-a ⟩
      - ∣ a ∣  ≤⟨ neg-antimono-≤ (0≤∣p∣ a) ⟩
      0ℚ       ≤⟨ 0≤∣p∣ a ⟩
      ∣ a ∣    ∎
  }

-∣-∣≤ : (a : ℚ) → - ∣ a ∣ ≤ a
-∣-∣≤ a =
  begin
  - ∣ a ∣    ≡˘⟨ cong -_ (∣-p∣≡∣p∣ a) ⟩
  - ∣ - a ∣  ≤⟨ neg-antimono-≤ (≤∣-∣ (- a)) ⟩
  - (- a)    ≡⟨ neg-neg a ⟩
  a          ∎

∣a-b∣≡∣b-a∣ : (a b : ℚ) → ∣ a - b ∣ ≡ ∣ b - a ∣
∣a-b∣≡∣b-a∣ a b =
  begin-equality
  ∣ a - b ∣          ≡⟨ sym (∣-p∣≡∣p∣ (a - b)) ⟩
  ∣ - (a - b) ∣      ≡⟨ cong ∣_∣ (neg-diff a b) ⟩
  ∣ b - a ∣          ∎


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

subtract-add-lemma : (a b : ℚ) → (a - b) + b ≡ a
subtract-add-lemma a b =
  begin-equality
  ((a - b) + b)    ≡⟨ +-assoc a (- b) b ⟩
  (a + (- b + b))  ≡⟨ cong (a +_) (+-inverseˡ b) ⟩
  (a + 0ℚ)         ≡⟨ +-identityʳ a ⟩
  a                ∎

add-difference-lemma : (a b : ℚ) → a + (b - a) ≡ b
add-difference-lemma a b =
  begin-equality
  a + (b - a)   ≡⟨ +-comm a (b - a) ⟩
  (b - a) + a   ≡⟨ subtract-add-lemma b a ⟩
  b             ∎

insert-lemma : (a b c : ℚ) → a - c ≡ (a - b) + (b - c)
insert-lemma a b c =
  begin-equality
  a - c                 ≡˘⟨ cong (_- c) (subtract-add-lemma a b) ⟩
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

triangle-inequality-proof-scheme :
  (a b c : ℚ) →
  {ab bc ac : ℚ} →
  ∣ a - b ∣ ≤ ab →
  ∣ b - c ∣ ≤ bc →
  ab + bc ≤ ac →
  ∣ a - c ∣ ≤ ac
triangle-inequality-proof-scheme = {!!}


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
        ∣ b - b' ∣    ≡⟨ ∣∣≡ ⟩
        b - b'        ≤⟨ +-mono-≤ b≤c (neg-antimono-≤ a≤b') ⟩
        c - a         ∎
    ; (inj₂ ∣∣≡-) →
        begin
        ∣ b - b' ∣    ≡⟨ ∣∣≡- ⟩
        - (b - b')    ≡⟨ neg-diff b b' ⟩
        b' - b        ≤⟨ +-mono-≤ b'≤c (neg-antimono-≤ a≤b) ⟩
        c - a         ∎
    }
