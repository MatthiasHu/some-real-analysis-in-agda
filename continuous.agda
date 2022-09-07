module continuous where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Function.Base using (case_of_)

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import real as ℝ using (ℝ; Cauchy; 0ℝ; _≃_; fromℚ; approxSplit; fromℚ-preserves-<)

open import preliminaries.on-rationals
open import preliminaries.convex-combination



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

module IVT
  (f : cont)
  (f-inc : strictly-increasing f)
  where

  record correct (c d : ℚ) : Set where
    field
      c<d : c ℚ.< d
      fc≤0 : capp f (fromℚ c) ℝ.≤ 0ℝ
      0≤fd : 0ℝ ℝ.≤ capp f (fromℚ d)

  module Step
    (c d : ℚ)
    (cd-correct : correct c d)
    where

    record conclusion : Set where
      field
        c' : ℚ
        d' : ℚ
        corr : correct c' d'
        c-mono : c ℚ.≤ c'
        d-mono : d' ℚ.≤ d
        cd-dist : d' ℚ.- c' ≡ 2/3 ℚ.* (d ℚ.- c)

    open correct cd-correct
    open ConvexCombination c d c<d

    c₀ = convex-comb 1/3
    d₀ = convex-comb 2/3

    c₀<d₀ : c₀ ℚ.< d₀
    c₀<d₀ = convex-comb-mono 1/3 2/3 (from-yes (1/3 ℚ.<? 2/3))
    c<c₀ : c ℚ.< c₀
    c<c₀ = convex-comb-mono-0 1/3 (from-yes (0ℚ ℚ.<? 1/3))
    c<d₀ : c ℚ.< d₀
    c<d₀ = convex-comb-mono-0 2/3 (from-yes (0ℚ ℚ.<? 2/3))
    c₀<d : c₀ ℚ.< d
    c₀<d = convex-comb-mono-1 1/3 (from-yes (1/3 ℚ.<? 1ℚ))
    d₀<d : d₀ ℚ.< d
    d₀<d = convex-comb-mono-1 2/3 (from-yes (2/3 ℚ.<? 1ℚ))

    split : 0ℝ ℝ.≤ capp f (fromℚ d₀) ⊎ capp f (fromℚ c₀) ℝ.≤ 0ℝ
    split = approxSplit
              (capp f (fromℚ c₀))
              (capp f (fromℚ d₀))
              0ℝ
              (f-inc (fromℚ c₀) (fromℚ d₀) (fromℚ-preserves-< c₀ d₀ c₀<d₀))

    IVTAux : conclusion
    IVTAux =
      case split of λ
      { (inj₁ 0≤fd₀) → record
          { c' = c
          ; d' = d₀
          ; corr = record
            { c<d = c<d₀
            ; fc≤0 = fc≤0
            ; 0≤fd = 0≤fd₀
            }
          ; c-mono = ℚ.≤-refl
          ; d-mono = ℚ.<⇒≤ d₀<d
          ; cd-dist = convex-comb-diff-0 2/3
          }
      ; (inj₂ fc₀≤0) → record
          { c' = c₀
          ; d' = d
          ; corr = record
            { c<d = c₀<d
            ; fc≤0 = fc₀≤0
            ; 0≤fd = 0≤fd
            }
          ; c-mono = ℚ.<⇒≤ c<c₀
          ; d-mono = ℚ.≤-refl
          ; cd-dist = convex-comb-diff-1 1/3
          }
      }

  module Iteration
    (a b : ℚ)
    (ab-correct : correct a b)
    (b-a≤1 : b ℚ.- a ℚ.≤ 1ℚ)
    where

    open ℚ.≤-Reasoning

    cs : ℕ → ℚ
    ds : ℕ → ℚ
    cds-correct : (n : ℕ) → correct (cs n) (ds n)
    step-conclusions : (n : ℕ) → Step.conclusion (cs n) (ds n) (cds-correct n)

    cs zero = a
    cs (suc n) = Step.conclusion.c' (step-conclusions n)

    ds zero = b
    ds (suc n) = Step.conclusion.d' (step-conclusions n)

    cds-correct zero = ab-correct
    cds-correct (suc n) = Step.conclusion.corr (step-conclusions n)

    step-conclusions n = Step.IVTAux (cs n) (ds n) (cds-correct n)

    module _
      (n : ℕ)
      where

      open Step.conclusion (step-conclusions n)

      cs-mono-suc : cs n ℚ.≤ cs (suc n)
      cs-mono-suc = c-mono

      ds-mono-suc : ds (suc n) ℚ.≤ ds n
      ds-mono-suc = d-mono

      cds-dist-suc : (ds (suc n)) ℚ.- (cs (suc n)) ≡ 2/3 ℚ.* (ds n ℚ.- cs n)
      cds-dist-suc = cd-dist

    cds-dist : (k : ℕ) → ds k ℚ.- cs k ≡ (2/3 ^ k) ℚ.* (b ℚ.- a)
    cds-dist zero =
      begin-equality
      ds zero ℚ.- cs zero           ≡⟨ refl ⟩
      b ℚ.- a                       ≡˘⟨ ℚ.*-identityˡ (b ℚ.- a) ⟩
      1ℚ ℚ.* (b ℚ.- a)              ≡⟨ refl ⟩
      (2/3 ^ zero) ℚ.* (b ℚ.- a)    ∎
    cds-dist (suc k) =
      begin-equality
      ds (suc k) ℚ.- cs (suc k)        ≡⟨ cds-dist-suc k ⟩
      2/3 ℚ.* (ds k ℚ.- cs k)          ≡⟨ cong (2/3 ℚ.*_) (cds-dist k) ⟩
      2/3 ℚ.* (2/3 ^ k ℚ.* (b ℚ.- a))  ≡˘⟨ ℚ.*-assoc 2/3 (2/3 ^ k) (b ℚ.- a) ⟩
      (2/3 ℚ.* 2/3 ^ k) ℚ.* (b ℚ.- a)  ≡⟨ refl ⟩
      2/3 ^ (suc k) ℚ.* (b ℚ.- a)      ∎

    cs-mono : (k n : ℕ) → (k ℕ.≤ n) → (cs k ℚ.≤ cs n)
    cs-mono k n k≤n = subst (λ n' → cs k ℚ.≤ cs n') (ℕ.m∸n+n≡m k≤n) (helper (n ℕ.∸ k) )
      where
      helper : (diff : ℕ) → cs k ℚ.≤ cs (diff ℕ.+ k)
      helper zero = ℚ.≤-refl
      helper (suc diff) =
        begin
        cs k             ≤⟨ helper diff ⟩
        cs (diff ℕ.+ k)     ≤⟨ cs-mono-suc (diff ℕ.+ k) ⟩
        cs (suc diff ℕ.+ k)  ∎

    ds-mono : (k n : ℕ) → (k ℕ.≤ n) → (ds n ℚ.≤ ds k)
    ds-mono k n k≤n =  subst (λ n' → ds n' ℚ.≤ ds k) (ℕ.m∸n+n≡m k≤n) (helper (n ℕ.∸ k) ) 
      where
      helper : (diff : ℕ) → ds (diff ℕ.+ k) ℚ.≤ ds k
      helper zero = ℚ.≤-refl
      helper (suc diff) =
        begin
        ds (suc diff ℕ.+ k)    ≤⟨ ds-mono-suc (diff ℕ.+ k) ⟩
        ds (diff ℕ.+ k)       ≤⟨  helper diff  ⟩
        ds k                  ∎

    cs<ds : (n m : ℕ) → cs n ℚ.< ds m
    cs<ds n m =
      let n⊔m = n ℕ.⊔ m
      in
      begin-strict
      cs n    ≤⟨ cs-mono n n⊔m (ℕ.m≤m⊔n n m) ⟩
      cs n⊔m  <⟨ correct.c<d (cds-correct n⊔m) ⟩
      ds n⊔m  ≤⟨ ds-mono m n⊔m (ℕ.m≤n⊔m n m) ⟩
      ds m    ∎

    cauchy-helper :
      (k : ℕ) →
      (n m : ℕ) →
      (n ℕ.≥ k) → (m ℕ.≥ k) →
      ℚ.∣ cs m ℚ.- cs n ∣ ℚ.≤ (2/3 ^ k) ℚ.* (b ℚ.- a)
    cauchy-helper k n m n≥k m≥k =
      begin
      ℚ.∣ cs m ℚ.- cs n ∣                           ≡⟨ {!!} ⟩
      ℚ.∣ cs m ℚ.- cs k ∣ ℚ.+ ℚ.∣ cs k ℚ.- cs n ∣   ≡⟨ {!!} ⟩
      2/3 ^ k ℚ.* (b ℚ.- a)                         ∎

    x : ℝ
    ℝ.as x = cs
    ℝ.M x p0 = 2 ℕ.* p0
    ℝ.cauchy x = {!!}

    IVT : Σ ℝ (λ x → capp f x ≃ 0ℝ)
    IVT = x , {!!}
