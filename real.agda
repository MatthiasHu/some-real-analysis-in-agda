{-# OPTIONS --allow-unsolved-metas #-}

module real where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (true; false)

open import Function.Base using (case_of_)
open import Relation.Nullary

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import Agda.Builtin.Unit using (tt)


--- preliminaries on small rational numbers ---

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


--- Cauchy sequence property ---

Cauchy : (ℕ → ℚ) → (ℕ → ℕ) → Set
Cauchy as M =
  (p n m : ℕ) →
  n ℕ.≥ M p →
  m ℕ.≥ M p →
  ℚ.∣ as n ℚ.- as m ∣ ℚ.≤ ½ ^ p


--- definition of real number ---

record ℝ : Set where
  constructor realConstr
  field
    as : ℕ → ℚ
    M : ℕ → ℕ
    cauchy : Cauchy as M
    -- Should we require M to be monotonous?


--- equality of real numbers ---

_≃_ : ℝ → ℝ → Set
(realConstr as M _) ≃ (realConstr bs N _) =
  (p : ℕ) → ℚ.∣ as (M (suc p)) ℚ.- bs (N (suc p)) ∣ ℚ.≤ ½ ^ p

≃-refl : (x : ℝ) → x ≃ x
≃-refl (realConstr as M _) p = begin
  ℚ.∣ as (M (suc p)) ℚ.- as (M (suc p)) ∣  ≡⟨ cong ℚ.∣_∣ (ℚ.+-inverseʳ (as (M (suc p)))) ⟩
  ℚ.∣ 0ℚ ∣                                 ≡⟨⟩
  0ℚ                                       <⟨ 0ℚ<½^p p ⟩
  ½ ^ p                                    ∎
  where
  open ℚ.≤-Reasoning

-- TODO: ≃-symm
-- TODO: ≃-trans


--- rational numbers as real numbers ---

fromℚ : ℚ → ℝ
ℝ.as (fromℚ a) _ = a
ℝ.M (fromℚ a) _ = zero
ℝ.cauchy (fromℚ a) p _ _ _ _ = begin
  ℚ.∣ a ℚ.- a ∣  ≡⟨  cong ℚ.∣_∣ (ℚ.+-inverseʳ a)  ⟩
  0ℚ             <⟨ 0ℚ<½^p p ⟩
  ½ ^ p          ∎
  where
  open ℚ.≤-Reasoning


--- basic predicates of real numbers ---

nneg : ℝ → Set
nneg (realConstr as M cauchy) = (p : ℕ) → ℚ.- (½ ^ p) ℚ.≤ as (M p)

-- TODO: RealNNegChar

pos : ℝ → Set
pos (realConstr as M cauchy) = Σ ℕ (λ p → ½ ^ p ℚ.≤ as (M (suc p)))


--- arithmetic operations ---

private
  differenceOfSums :
    (a b a' b' : ℚ) →
    (a ℚ.+ b) ℚ.- (a' ℚ.+ b') ≡ (a ℚ.- a') ℚ.+ (b ℚ.- b')
  differenceOfSums = {!!}

_+_ : ℝ → ℝ → ℝ
ℝ.as (realConstr as M cauchy-as + realConstr bs N cauchy-bs) n = as n ℚ.+ bs n
ℝ.M (realConstr as M cauchy-as + realConstr bs N cauchy-bs) p = (M (suc p) ℕ.⊔ N (suc p))
ℝ.cauchy (realConstr as M cauchy-as + realConstr bs N cauchy-bs) p n m n≥ m≥ =
  begin
  ℚ.∣ (as n ℚ.+ bs n) ℚ.- (as m ℚ.+ bs m) ∣        ≡⟨ cong ℚ.∣_∣ (differenceOfSums (as n) (bs n) (as m) (bs m)) ⟩
  ℚ.∣ (as n ℚ.- as m) ℚ.+ (bs n ℚ.- bs m) ∣        ≤⟨ ℚ.∣p+q∣≤∣p∣+∣q∣ (as n ℚ.- as m) (bs n ℚ.- bs m) ⟩
  ℚ.∣ (as n ℚ.- as m) ∣ ℚ.+ ℚ.∣ (bs n ℚ.- bs m) ∣  ≤⟨ ℚ.+-mono-≤ (cauchy-as (suc p) n m (⊔-left n≥) (⊔-left m≥))
                                                                 (cauchy-bs (suc p) n m (⊔-right n≥) (⊔-right m≥)) ⟩
  (½ ^ suc p) ℚ.+ (½ ^ suc p)                      ≡⟨ ½^sucp+½^sucp≡½^p p ⟩
  ½ ^ p                                            ∎
  where
  open ℚ.≤-Reasoning
  ⊔-left : {k : ℕ} → (k ℕ.≥ M (suc p) ℕ.⊔ N (suc p)) → k ℕ.≥ M (suc p)
  ⊔-left = ℕ.m⊔n≤o⇒m≤o (M (suc p)) (N (suc p))
  ⊔-right : {k : ℕ} → (k ℕ.≥ M (suc p) ℕ.⊔ N (suc p)) → k ℕ.≥ N (suc p)
  ⊔-right = ℕ.m⊔n≤o⇒n≤o (M (suc p)) (N (suc p))

-_ : ℝ → ℝ
ℝ.as (- realConstr as M cauchy) n = ℚ.- as n
ℝ.M (- realConstr as M cauchy) = M
ℝ.cauchy (- realConstr as M cauchy) = {!!}

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)


--- comparison of reals ---

_<_ : ℝ → ℝ → Set
x < y = pos (y - x)

_≤_ : ℝ → ℝ → Set
x ≤ y = nneg (y - x)


--- approxSplit ---

approxSplit : (x y z : ℝ) → x < y → (z ≤ y) ⊎ (x ≤ z)
approxSplit (realConstr as M cauchy) (realConstr bs N cauchy₁) (realConstr cs L cauchy₂) (p , snd) =
  let n = N (suc (suc p)) ℕ.⊔ M (suc (suc p))
      m = n ℕ.⊔ L (suc (suc p))
  in
  case (cs m ℚ.≤? ½ ℚ.* (as n ℚ.+ bs n)) of λ
    { (yes ineq) → inj₁ (λ p₁ → {!!})
    ; (no ¬p) → inj₂ {!!}
    }

