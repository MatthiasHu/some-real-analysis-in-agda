{-# OPTIONS --allow-unsolved-metas #-}

module real where

-- We use version 1.7.1 of the agda standard library.

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Rational as ℚ using (ℚ; ½; -½; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (true; false)

open import Function.Base using (case_of_)
open import Relation.Nullary

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import preliminaries.on-rationals


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

-- Should we do the characterization for _≤_ instead of _≃_ ?
module ≃-Characterization
  (x@(realConstr as M cauchy-as) : ℝ)
  (y@(realConstr bs N cauchy-bs) : ℝ)
  where

  Characterization : Set
  Characterization =
    (p : ℕ) →
    Σ ℕ (λ k →
      (n m : ℕ) →
      n ℕ.≥ k →
      ℚ.∣ as n ℚ.- bs n ∣ ℚ.≤ ½ ^ p)

  to-characterization : x ≃ y → Characterization
  to-characterization x≃y p =
      k
    , λ n n≥k → {!
        triangle-inequality-proof-scheme (as n) (as k1) (bs m)
          (cauchy-as (suc p) n k1 (ℕ.m⊔n≤o⇒m≤o k1 k2 n≥k ) (ℕ.≤-reflexive refl))
          {!!}
          {!!}
          !}
    where
    k1 = M (suc p)
    k2 = N (suc p)
    k = k1 ℕ.⊔ k2
    open ℚ.≤-Reasoning

  from-characterization : Characterization → x ≃ y
  from-characterization char p = {!!}

≃-refl : (x : ℝ) → x ≃ x
≃-refl (realConstr as M _) p = begin
  ℚ.∣ as (M (suc p)) ℚ.- as (M (suc p)) ∣  ≡⟨ cong ℚ.∣_∣ (ℚ.+-inverseʳ (as (M (suc p)))) ⟩
  ℚ.∣ 0ℚ ∣                                 ≡⟨⟩
  0ℚ                                       <⟨ 0ℚ<½^p p ⟩
  ½ ^ p                                    ∎
  where
  open ℚ.≤-Reasoning

≃-symm : (x y : ℝ) → x ≃ y → y ≃ x
≃-symm (realConstr as M cauchy-as) (realConstr bs N cauchy-bs) x≃y p =
  begin
  ℚ.∣ bs (N (suc p)) ℚ.- as (M (suc p)) ∣  ≡⟨ ∣a-b∣≡∣b-a∣ (bs (N (suc p))) (as (M (suc p))) ⟩
  ℚ.∣ as (M (suc p)) ℚ.- bs (N (suc p)) ∣  ≤⟨ x≃y p ⟩
  ½ ^ p  ∎
  where
  open ℚ.≤-Reasoning

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

0ℝ = fromℚ 0ℚ


--- basic predicates of real numbers ---

nneg : ℝ → Set
nneg (realConstr as M cauchy) = (p : ℕ) → ℚ.- (½ ^ p) ℚ.≤ as (M p)

-- TODO: RealNNegChar

pos : ℝ → Set
pos (realConstr as M cauchy) = Σ ℕ (λ p → ½ ^ p ℚ.≤ as (M (suc p)))

module pos-Characterizations
  (x@(realConstr as M cauchy) : ℝ)
  where

  EpsilonAndIndexBound : Set
  EpsilonAndIndexBound = Σ ℕ (λ p → Σ ℕ (λ k → (n : ℕ) → n ℕ.≥ k → as n ℚ.≥ ½ ^ p))

  StrictEpsilonAndIndexBound : Set
  StrictEpsilonAndIndexBound = Σ ℕ (λ p → Σ ℕ (λ k → (n : ℕ) → n ℕ.≥ k → as n ℚ.> ½ ^ p))

  StrictEpsilonAndIndexBound→EpsilonAndIndexBound :
    StrictEpsilonAndIndexBound → EpsilonAndIndexBound
  StrictEpsilonAndIndexBound→EpsilonAndIndexBound (p , k , as>½^p) =
      p , k , λ n n≥k → ℚ.<⇒≤ (as>½^p n n≥k)

  EpsilonAndIndexBound→StrictEpsilonAndIndexBound :
    EpsilonAndIndexBound → StrictEpsilonAndIndexBound
  EpsilonAndIndexBound→StrictEpsilonAndIndexBound (p , k , as≥½^p) =
    suc p , k , λ n n≥k → ℚ.<-≤-trans (½^sucp<½^p p) (as≥½^p n n≥k)

  pos→EpsilonAndIndexBound : pos x → EpsilonAndIndexBound
  pos→EpsilonAndIndexBound (p , ½^p≤asMsucp) =
    let k = M (suc p)
    in
    suc p , k , λ n n≥k →
    begin
    ½ ^ suc p                           ≡⟨ cong (ℚ._* (½ ^ p)) (refl {x = ½}) ⟩
    (-½ ℚ.+ 1ℚ) ℚ.* ½ ^ p               ≡⟨ ℚ.*-distribʳ-+ (½ ^ p) -½ 1ℚ ⟩
    -½ ℚ.* ½ ^ p ℚ.+ 1ℚ ℚ.* ½ ^ p       ≡⟨ cong₂ ℚ._+_ (sym (ℚ.neg-distribˡ-* ½ (½ ^ p))) (ℚ.*-identityˡ (½ ^ p)) ⟩
    ℚ.- ½ ^ suc p           ℚ.+ ½ ^ p   ≤⟨ ℚ.+-mono-≤ (ℚ.neg-antimono-≤ (cauchy (suc p) n k n≥k ℕ.≤-refl))
                                                        ½^p≤asMsucp ⟩
    ℚ.- ℚ.∣ as n ℚ.- as k ∣ ℚ.+ as k    ≤⟨ ℚ.+-monoˡ-≤ (as k) (-∣-∣≤ (as n ℚ.- as k)) ⟩
           (as n ℚ.- as k)  ℚ.+ as k    ≡⟨ subtract-add-lemma (as n) (as k) ⟩
    as n                                ∎
    where
    open ℚ.≤-Reasoning

-- nneg-pos : (x : ℝ) → nneg x


--- arithmetic operations ---

_+_ : ℝ → ℝ → ℝ
ℝ.as (realConstr as M cauchy-as + realConstr bs N cauchy-bs) n = as n ℚ.+ bs n
ℝ.M (realConstr as M cauchy-as + realConstr bs N cauchy-bs) p = (M (suc p) ℕ.⊔ N (suc p))
ℝ.cauchy (realConstr as M cauchy-as + realConstr bs N cauchy-bs) p n m n≥ m≥ =
  begin
  ℚ.∣ (as n ℚ.+ bs n) ℚ.- (as m ℚ.+ bs m) ∣        ≡⟨ cong ℚ.∣_∣ (difference-of-sums (as n) (bs n) (as m) (bs m)) ⟩
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
ℝ.cauchy (- realConstr as M cauchy) p n m n≥ m≥ =
  begin
  ℚ.∣ ℚ.- as n ℚ.- ℚ.- as m ∣    ≡˘⟨ cong ℚ.∣_∣ (ℚ.neg-distrib-+ (as n) (ℚ.- as m)) ⟩
  ℚ.∣ ℚ.- (as n ℚ.- as m) ∣      ≡⟨ ℚ.∣-p∣≡∣p∣ (as n ℚ.- as m) ⟩
  ℚ.∣ as n ℚ.- as m ∣            ≤⟨ cauchy p n m n≥ m≥ ⟩
  ½ ^ p                          ∎
  where
  open ℚ.≤-Reasoning

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)


--- comparison of reals ---

_<_ : ℝ → ℝ → Set
x < y = pos (y - x)

_≤_ : ℝ → ℝ → Set
x ≤ y = nneg (y - x)


--- approxSplit ---

approxSplit : (x y z : ℝ) → x < y → (z < y) ⊎ (x < z)
approxSplit
  (realConstr as M as-cauchy)
  (realConstr bs N bs-cauchy)
  (realConstr cs L cs-cauchy)
  (p , snd)
  =
  let n = N (suc (suc p)) ℕ.⊔ M (suc (suc p))
      m = n ℕ.⊔ L (suc (suc p))
  in
  case (cs m ℚ.≤? ½ ℚ.* (as n ℚ.+ bs n)) of λ
    { (yes ineq) → inj₁ {!!}
    ; (no ¬p) → inj₂ {!!}
    }


--- compatibility of fromℚ with various operations ---

fromℚ-preserves-pos : (a : ℚ) → ℚ.Positive a → pos (fromℚ a)
fromℚ-preserves-pos a a-positive =
  let (p , ½^p<a) = archimedian-ε a a-positive
  in p , ℚ.<⇒≤ ½^p<a

fromℚ-preserves-< : (a b : ℚ) → a ℚ.< b → fromℚ a < fromℚ b
fromℚ-preserves-< a b a<b = fromℚ-preserves-pos (b ℚ.- a) (ℚ.positive (
  begin-strict
  0ℚ        ≡˘⟨ ℚ.+-inverseʳ b ⟩
  b ℚ.- b   <⟨ ℚ.+-monoʳ-< b (ℚ.neg-antimono-< a<b) ⟩
  b ℚ.- a   ∎))
  where
  open ℚ.≤-Reasoning
