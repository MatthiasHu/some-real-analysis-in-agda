{-# OPTIONS --allow-unsolved-metas #-}

module continuous where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality hiding ([_])
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
    -- μ : ℚ
    -- ν : ℚ

    @0 cauchy : (a : ℚ) → Cauchy (h a) α
    @0 ucont :
      (a b : ℚ) →
      (p n : ℕ) →
      α p ℕ.≤ n →
      ℚ.∣ a ℚ.- b ∣ ℚ.≤ ½ ^ (ω p) →
      ℚ.∣ h a n ℚ.- h b n ∣ ℚ.≤ ½ ^ p
    -- Do we need more?


--- application of a continuous function to a real number ---

capp : cont → ℝ → ℝ
ℝ.as (capp f (ℝ.realConstr as M cauchy-as)) n = cont.h f (as n) n 
ℝ.M (capp f (ℝ.realConstr as M cauchy-as)) p = cont.α f (suc p) ℕ.⊔ M (cont.ω f (suc p))
ℝ.cauchy (capp (contConstr h α ω cauchy-h ucont) (ℝ.realConstr as M cauchy-as)) p n m n≥ m≥ =
  begin
  ℚ.∣ h (as n) n ℚ.- h (as m) m ∣
       ≤⟨ triangle-inequality (h (as n) n) (h (as n) m) (h (as m) m) ⟩
  ℚ.∣ h (as n) n ℚ.- h (as n) m ∣ ℚ.+ ℚ.∣ h (as n) m ℚ.- h (as m) m ∣
       ≤⟨ ℚ.+-mono-≤ (cauchy-h (as n) (suc p) n m n≥α m≥α)
                     (ucont (as n) (as m) (suc p) m m≥α (cauchy-as (ω (suc p)) n m n≥M m≥M)) ⟩
  (½ ^ (suc p)) ℚ.+ (½ ^ (suc p))
       ≡⟨ ½^sucp+½^sucp≡½^p p ⟩
  ½ ^ p
       ∎
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

@0 capp-preserves-≃ : (f : cont) → (x x' : ℝ) → x ≃ x' → capp f x ≃ capp f x'
capp-preserves-≃
  (contConstr h α ω cauchy-h ucont)
  (ℝ.realConstr as M cauchy-as)
  (ℝ.realConstr bs N cauchy-bs)
  x≃x'
  p
  =
  triangle-inequality-proof-scheme (h (as m) m) (h (as m) n) (h (bs n) n)
    (begin
      ℚ.∣ h (as m) m ℚ.- h (as m) n ∣   ≤⟨ cauchy-h (as m) (suc (suc p)) m n (ℕ.m≤m⊔n _ _) (ℕ.m≤m⊔n _ _) ⟩
      ½ ^ suc (suc p)                   ≤⟨ {!!} ⟩
      ½ ^ suc p                         ∎)
    (begin
      ℚ.∣ h (as m) n ℚ.- h (bs n) n ∣   ≤⟨ ucont (as m) (bs n) (suc (suc p)) n (ℕ.m≤m⊔n _ _)
                                            {!x≃x' (ω (suc p))!} ⟩
      ½ ^ suc (suc p)                   ≤⟨ {!!} ⟩
      ½ ^ suc p                         ∎)
    (ℚ.≤-reflexive (½^sucp+½^sucp≡½^p p))
  where
  open ℚ.≤-Reasoning
  m = α (suc (suc p)) ℕ.⊔ M (ω (suc (suc p)))
  n = α (suc (suc p)) ℕ.⊔ N (ω (suc (suc p)))


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

  record correct-pair : Set where
    field
      c : ℚ
      d : ℚ
      cd-correct : correct c d

  module Step
    (correct-cd : correct-pair)
    where

    open correct-pair correct-cd

    record conclusion : Set where
      field
        correct-c'd' : correct-pair

      open correct-pair correct-c'd' public
        renaming
          ( c to c'
          ; d to d'
          ; cd-correct to c'd'-correct
          )

      field
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

    -- It was important for execution performance to use the [_,_]′ operator
    -- instead of a pattern lambda here.
    -- Remember that both pattern lambdas and definitions in a parametrized
    -- module are "lifted" to the global scope...

    IVTAux : conclusion
    IVTAux =
      [ (λ 0≤fd₀ → record
          { correct-c'd' = record
            { c = c
            ; d = d₀
            ; cd-correct = record
              { c<d = c<d₀
              ; fc≤0 = fc≤0
              ; 0≤fd = 0≤fd₀
              }
            }
          ; c-mono = ℚ.≤-refl
          ; d-mono = ℚ.<⇒≤ d₀<d
          ; cd-dist = convex-comb-diff-0 2/3
          }
        )
      , (λ fc₀≤0 → record
          { correct-c'd' = record
            { c = c₀
            ; d = d
            ; cd-correct = record
              { c<d = c₀<d
              ; fc≤0 = fc₀≤0
              ; 0≤fd = 0≤fd
              }
            }
          ; c-mono = ℚ.<⇒≤ c<c₀
          ; d-mono = ℚ.≤-refl
          ; cd-dist = convex-comb-diff-1 1/3
          }
        )
      ]′
      split

  module Iteration
    (a b : ℚ)
    (ab-correct : correct a b)
    (b-a≤1 : b ℚ.- a ℚ.≤ 1ℚ)
    where

    open ℚ.≤-Reasoning

    -- We must be careful to avoid any branching in the mutually recursive definition.
    -- Otherwise we would get exponential running time.
    -- It seems like we can not even decompose and put back together a record.
    -- And there might be more things we are still doing wrong.

    correct-cds : ℕ → correct-pair
    step-conclusions : (n : ℕ) → Step.conclusion (correct-cds n)

    correct-cds zero =
      record
      { c = a
      ; d = b
      ; cd-correct = ab-correct
      }
    correct-cds (suc n) =
      Step.conclusion.correct-c'd' (step-conclusions n)

    step-conclusions n = Step.IVTAux (correct-cds n)

    cs : ℕ → ℚ
    cs n = correct-pair.c (correct-cds n)

    ds : ℕ → ℚ
    ds n = correct-pair.d (correct-cds n)

    cds-correct : (n : ℕ) → correct (cs n) (ds n)
    cds-correct n = correct-pair.cd-correct (correct-cds n)

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
        cs k                 ≤⟨ helper diff ⟩
        cs (diff ℕ.+ k)      ≤⟨ cs-mono-suc (diff ℕ.+ k) ⟩
        cs (suc diff ℕ.+ k)  ∎

    ds-mono : (k n : ℕ) → (k ℕ.≤ n) → (ds n ℚ.≤ ds k)
    ds-mono k n k≤n =  subst (λ n' → ds n' ℚ.≤ ds k) (ℕ.m∸n+n≡m k≤n) (helper (n ℕ.∸ k) )
      where
      helper : (diff : ℕ) → ds (diff ℕ.+ k) ℚ.≤ ds k
      helper zero = ℚ.≤-refl
      helper (suc diff) =
        begin
        ds (suc diff ℕ.+ k)   ≤⟨ ds-mono-suc (diff ℕ.+ k) ⟩
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

    cs∈[cs,ds] : {k n : ℕ} → (k ℕ.≤ n) → cs n ∈[ cs k , ds k ]
    cs∈[cs,ds] {k} {n} k≤n =
        cs-mono k n k≤n
      , ℚ.<⇒≤ (cs<ds n k)

    ds∈[cs,ds] : {k n : ℕ} → (k ℕ.≤ n) → ds n ∈[ cs k , ds k ]
    ds∈[cs,ds] {k} {n} k≤n =
        ℚ.<⇒≤ (cs<ds k n)
      , ds-mono k n k≤n

    cauchy-helper :
      (k : ℕ) →
      (n m : ℕ) →
      (n ℕ.≥ k) → (m ℕ.≥ k) →
      ℚ.∣ cs n ℚ.- cs m ∣ ℚ.≤ (2/3 ^ k) ℚ.* (b ℚ.- a)
    cauchy-helper k n m n≥k m≥k =
      begin
      ℚ.∣ cs n ℚ.- cs m ∣     ≤⟨ dist-interval (cs k) (ds k) (cs n) (cs m)
                                               (cs∈[cs,ds] n≥k) (cs∈[cs,ds] m≥k) ⟩
      ds k ℚ.- cs k           ≡⟨ cds-dist k ⟩
      2/3 ^ k ℚ.* (b ℚ.- a)   ∎

    x : ℝ
    ℝ.as x = cs
    ℝ.M x p = 2 ℕ.* p
    ℝ.cauchy x p n m n≥ m≥ =
      begin
      ℚ.∣ cs n ℚ.- cs m ∣            ≤⟨ cauchy-helper (2 ℕ.* p) n m n≥ m≥ ⟩
      2/3 ^ (2 ℕ.* p) ℚ.* (b ℚ.- a)  ≡⟨ cong (λ c → c ℚ.* (b ℚ.- a)) (sym (^-assocʳ 2/3 2 p)) ⟩
      (2/3 ^ 2)^ p ℚ.* (b ℚ.- a)     ≤⟨ ℚ.*-monoˡ-≤-pos ((2/3 ^ 2)^ p)
                                                        (ℚ.positive (0ℚ<a^p (2/3 ^ 2) 0<4/9 p))
                                                        b-a≤1 ⟩
      (2/3 ^ 2)^ p ℚ.* 1ℚ            ≡⟨ ℚ.*-identityʳ ((2/3 ^ 2)^ p) ⟩
      (2/3 ^ 2)^ p                   ≤⟨ {!!} ⟩
      ½ ^ p                          ∎
      where
      0<4/9 : 0ℚ ℚ.< (2/3 ^ 2)
      0<4/9 = from-yes (0ℚ ℚ.<? (2/3 ^ 2))
      4/9≤½ : 2/3 ^ 2 ℚ.≤ ½
      4/9≤½ = from-yes (2/3 ^ 2 ℚ.≤? ½)

    IVT : Σ ℝ (λ x → capp f x ≃ 0ℝ)
    IVT = x , {!!}
