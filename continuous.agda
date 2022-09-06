
module continuous where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ using ()
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Function.Base using (case_of_)

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import real as ℝ using (ℝ; Cauchy; ½^sucp+½^sucp≡½^p; 0ℝ; _≃_; fromℚ; approxSplit; fromℚ-preserves-<)


--- definition of continuous functions ---

-- continuous functions represented by approximations of their values on the rationals

record cont : Set where
  constructor contConstr
  field
    h : ℚ → ℕ → ℚ
    α : ℕ → ℕ
    ω : ℕ → ℕ
    μ : ℚ
    ν : ℚ

    cauchy : (a : ℚ) → Cauchy (h a) α
    ucont : (a b : ℚ) → (p n : ℕ) → α p ℕ.≤ n → ℚ.∣ a ℚ.- b ∣ ℚ.≤ ½ ^ (ω p) → ℚ.∣ h a n ℚ.- h b n ∣ ℚ.≤ ½ ^ p
    -- Do we need more?


--- application of a continuous function to a real number ---

insert-lemma : (a b c : ℚ) → a ℚ.- c ≡ (a ℚ.- b) ℚ.+ (b ℚ.- c)
insert-lemma a b c =
  begin-equality
  a - c                     ≡˘⟨ cong (_- c) (ℚ.+-identityʳ a) ⟩
  (a + 0ℚ) - c              ≡˘⟨ cong (λ z → (a + z) - c) (ℚ.+-inverseˡ b) ⟩
  (a + (- b + b)) - c       ≡˘⟨ cong (_- c) (ℚ.+-assoc a (- b) b) ⟩
  ((a - b) + b) - c         ≡⟨ ℚ.+-assoc (a - b) b (- c) ⟩
  (a - b) + (b - c)         ∎
  where
  open ℚ.≤-Reasoning
  open import Data.Rational -- for unqualified _+_ and _-_

capp : cont → ℝ → ℝ
ℝ.as (capp f (ℝ.realConstr as M cauchy-as)) n = cont.h f (as n) n 
ℝ.M (capp f (ℝ.realConstr as M cauchy-as)) p = cont.α f (suc p) ℕ.⊔ M (cont.ω f (suc p))
ℝ.cauchy (capp (contConstr h α ω μ ν cauchy-h ucont) (ℝ.realConstr as M cauchy-as)) p n m n≥ m≥ =
  begin
  ℚ.∣ h (as n) n ℚ.- h (as m) m ∣
       ≡⟨ cong ℚ.∣_∣ (insert-lemma (h (as n) n) (h (as n) m) (h (as m) m)) ⟩
  ℚ.∣ (h (as n) n ℚ.- h (as n) m) ℚ.+ (h (as n) m ℚ.- h (as m) m) ∣
       ≤⟨ ℚ.∣p+q∣≤∣p∣+∣q∣ ( h (as n) n ℚ.- h (as n) m) ( h (as n) m ℚ.- h (as m) m) ⟩
  ℚ.∣ h (as n) n ℚ.- h (as n) m ∣ ℚ.+ ℚ.∣ h (as n) m ℚ.- h (as m) m ∣
       ≤⟨ ℚ.+-mono-≤ (cauchy-h (as n) (suc p) n m n≥α m≥α)
                     (ucont (as n) (as m) (suc p) m m≥α (cauchy-as (ω (suc p)) n m n≥M m≥M)) ⟩
  (½ ^ (suc p)) ℚ.+ (½ ^ (suc p))
       ≡⟨ ½^sucp+½^sucp≡½^p p ⟩
  ½ ^ p    ∎
  where
  open ℚ.≤-Reasoning
  n≥α : n ℕ.≥ α (suc p)
  n≥α = (ℕ.m⊔n≤o⇒m≤o (α (suc p)) (M (ω (suc p))) n≥)
  n≥M : n ℕ.≥ M (ω (suc p))
  n≥M = (ℕ.m⊔n≤o⇒n≤o (α (suc p)) (M (ω (suc p))) n≥)
  m≥α : m ℕ.≥ α (suc p)
  m≥α = (ℕ.m⊔n≤o⇒m≤o (α (suc p)) (M (ω (suc p))) m≥)
  m≥M : m ℕ.≥ M (ω (suc p))
  m≥M = (ℕ.m⊔n≤o⇒n≤o (α (suc p)) (M (ω (suc p))) m≥)

-- TODO: capp-preserves-≃


--- increasing functions ---

strictly-increasing : cont → Set
strictly-increasing f = (x y : ℝ) → x ℝ.< y → capp f x ℝ.< capp f y
  

--- intermediate value theorem ---

1/3 = ℤ.+ 1 ℚ./ 3
2/3 = ℤ.+ 2 ℚ./ 3

module ConvexCombination
  (c d : ℚ)
  (c<d : c ℚ.< d)
  where

  open import Data.Rational
  open ℚ.≤-Reasoning

  convex-comb : ℚ → ℚ
  convex-comb t = c + t * (d - c)

  convex-comb-0 : convex-comb 0ℚ ≡ c
  convex-comb-0 =
    begin-equality
    c + 0ℚ * (d - c)   ≡⟨ cong (c +_) (ℚ.*-zeroˡ (d - c)) ⟩
    c + 0ℚ             ≡⟨ ℚ.+-identityʳ c ⟩
    c                  ∎

  convex-comb-1 : convex-comb 1ℚ ≡ d
  convex-comb-1 =
    begin-equality
    c + 1ℚ * (d - c)  ≡⟨ cong (c +_) (ℚ.*-identityˡ (d - c)) ⟩
    c + (d - c)       ≡⟨ cong (c +_) (ℚ.+-comm d (- c)) ⟩
    c + ((- c) + d)   ≡˘⟨ ℚ.+-assoc c (- c) d ⟩
    (c - c) + d       ≡⟨ cong (_+ d) (ℚ.+-inverseʳ c) ⟩
    0ℚ + d            ≡⟨ ℚ.+-identityˡ d  ⟩
    d                 ∎

  d-c-Positive : Positive (d - c)
  d-c-Positive = positive
    (begin-strict
    0ℚ       ≡˘⟨ ℚ.+-inverseʳ c ⟩
    c - c    <⟨ ℚ.+-monoˡ-< (- c) c<d ⟩
    d - c    ∎)

  convex-comb-mono :
    {t t' : ℚ} →
    t ℚ.< t' →
    convex-comb t ℚ.< convex-comb t'
  convex-comb-mono {t} {t'} t<t' = ℚ.+-monoʳ-< c
    (begin-strict
    t * (d - c)    <⟨ ℚ.*-monoˡ-<-pos (d - c) d-c-Positive t<t' ⟩
    t' * (d - c)   ∎
    )

module IVT
  (f : cont)
  (f-inc : strictly-increasing f)
  where

  record correct (c d : ℚ) : Set where
    constructor mkCorrect
    field
      c<d : c ℚ.< d
      fc≤0 : capp f (fromℚ c) ℝ.≤ 0ℝ
      0≤fd : 0ℝ ℝ.≤ capp f (fromℚ d)

  record compatible (c d c' d' : ℚ) : Set where
    field
      c-mono : c ℚ.≤ c'
      d-mono : d' ℚ.≤ d
      d-c : d' ℚ.- c' ≡ 2/3 ℚ.* (d ℚ.- c)

  IVTAux :
    (c d : ℚ) →
    (correct c d) →
    Σ (ℚ × ℚ) (λ (c' , d') → correct c' d' × compatible c d c' d')
  IVTAux c d  (mkCorrect c<d fc≤0 0≤fd) =
    let open ConvexCombination c d c<d
        c₀ = convex-comb 1/3
        d₀ = convex-comb 2/3
        c₀<d₀ : c₀ ℚ.< d₀
        c₀<d₀ = convex-comb-mono ((from-yes (1/3 ℚ.<? 2/3)))
        split = approxSplit
                  (capp f (fromℚ c₀))
                  (capp f (fromℚ d₀))
                  0ℝ
                  (f-inc (fromℚ c₀) (fromℚ d₀) (fromℚ-preserves-< c₀ d₀ c₀<d₀))
        open ℚ.≤-Reasoning
        c<d₀ : c ℚ.< d₀
        c<d₀ = begin-strict
                 c               ≡˘⟨ convex-comb-0 ⟩
                 convex-comb 0ℚ  <⟨ convex-comb-mono ((from-yes (0ℚ ℚ.<? 2/3))) ⟩
                 d₀              ∎
        c₀<d : c₀ ℚ.< d
        c₀<d = begin-strict
                 c₀              <⟨ convex-comb-mono ((from-yes (1/3 ℚ.<? 1ℚ))) ⟩
                 convex-comb 1ℚ  ≡⟨ convex-comb-1 ⟩
                 d               ∎
    in
    case split of λ
      { (inj₁ 0≤fd₀) →
          (c , d₀)
        , ( record
            { c<d = {!c<d₀!}
            ; fc≤0 = fc≤0
            ; 0≤fd = 0≤fd₀
            }
          , record
            { c-mono = ℚ.≤-refl
            ; d-mono = {!!}
            ; d-c = {!!}
            }
          )
    ; (inj₂ fc₀≤0) →
        (c₀ , d)
      , ( record
          { c<d = c₀<d
          ; fc≤0 = fc₀≤0
          ; 0≤fd = 0≤fd
          }
        , record
          { c-mono = {!!}
          ; d-mono = ℚ.≤-refl
          ; d-c = {!!}
          }
        )
      }

{-
  IVT :
    RecData →
    Σ ℝ (λ z → capp f z ≃ 0ℝ)
  IVT = {!!}
-}
