
module continuous where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Integer as ℤ using ()
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ)
import Data.Rational.Properties as ℚ
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

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

  convex-combination : ℚ → ℚ
  convex-combination t = (1ℚ - t) * c + t * d

  convex-combination-0 : convex-combination 0ℚ ≡ c
  convex-combination-0 =
    begin-equality
    1ℚ * c + 0ℚ * d  ≡⟨ cong₂ _+_ (ℚ.*-identityˡ c) (ℚ.*-zeroˡ d) ⟩
    c + 0ℚ           ≡⟨ ℚ.+-identityʳ c ⟩
    c                ∎

  convex-combination-1 : convex-combination 1ℚ ≡ d
  convex-combination-1 =
    begin-equality
    0ℚ * c + 1ℚ * d  ≡⟨ cong₂ _+_ (ℚ.*-zeroˡ c) (ℚ.*-identityˡ d) ⟩
    0ℚ + d           ≡⟨ ℚ.+-identityˡ d ⟩
    d                ∎

  convex-combination-mono :
    (t t' : ℚ) →
    t ℚ.< t' →
    convex-combination t ℚ.< convex-combination t'
  convex-combination-mono t t' t<t' =
    begin-strict
    (1ℚ - t) * c + t * d                ≡⟨ cong (_+ t * d) ( ℚ.*-distribʳ-+ c 1ℚ (- t) )  ⟩
    (1ℚ * c + (- t) * c) + t * d    ≡⟨ ℚ.+-assoc (1ℚ * c) ((- t) * c) (t * d) ⟩
    1ℚ * c + ((- t) * c + t * d)    <⟨ {!!} ⟩
    (1ℚ - t') * c + t' * d    ∎


c-d-lemma : (c d : ℚ) → (c ℚ.< d) → (2/3 ℚ.* c ℚ.+ 1/3 ℚ.* d) ℚ.< (1/3 ℚ.* c ℚ.+ 2/3 ℚ.* d)
c-d-lemma c d c<d = {!!}
  where
  open ℚ.≤-Reasoning

module IVT?
  (f : cont)
  (f-inc : strictly-increasing f)
  (a b : ℚ)
  (a<b : a ℚ.< b)
  (fa≤0 : capp f (fromℚ a) ℝ.≤ 0ℝ)
  (0≤fb : 0ℝ ℝ.≤ capp f (fromℚ b))
  where


  c,d,c<d : ℕ → Σ (ℚ × ℚ) (λ (c , d) → c ℚ.< d)
  c,d,c<d zero = (a , b) , a<b
  c,d,c<d (suc n) =
    let (c , d) , c<d = c,d,c<d n
        c₀ = 2/3 ℚ.* c ℚ.+ 1/3 ℚ.* d
        d₀ = 1/3 ℚ.* c ℚ.+ 2/3 ℚ.* d
        c₀<d₀ : c₀ ℚ.< d₀
        c₀<d₀ = c-d-lemma c d c<d
        split = approxSplit
                  (capp f (fromℚ c₀))
                  (capp f (fromℚ d₀))
                  0ℝ
                  (f-inc (fromℚ c₀) (fromℚ d₀) (fromℚ-preserves-< c₀ d₀ c₀<d₀))
    in
    case split of λ
      { (inj₁ 0≤fd₀) → (c , d₀) , {!!}
      ; (inj₂ fc₀≤0) → (c₀ , d) , {!!}
      }

  c d : ℕ → ℚ
  c n = proj₁ (proj₁ (c,d,c<d n))
  d n = proj₂ (proj₁ (c,d,c<d n))

  step-d-c : (n : ℕ) → d (suc n) ℚ.- c (suc n) ≡ 2/3 ℚ.* (d n ℚ.- c n)
  step-d-c n = {!d (suc n)!}


module IVT
  (f : cont)
  (f-inc : strictly-increasing f)
  where

  record RecData : Set where
    constructor recData
    field
      c : ℚ
      d : ℚ
      c<d : c ℚ.< d
      fc≤0 : capp f (fromℚ c) ℝ.≤ 0ℝ
      0≤fd : 0ℝ ℝ.≤ capp f (fromℚ d)

  record compatible (rd rd' : RecData) : Set where
    open RecData
    field
      c-mono : c rd ℚ.≤ c rd'
      d-mono : d rd' ℚ.≤ d rd
      d-c : d rd' ℚ.- c rd' ≡ 2/3 ℚ.* (d rd ℚ.- c rd)

  IVTAux :
    (rd : RecData) →
    Σ RecData (compatible rd)
  IVTAux (recData c d c<d fc≤0 0≤fd) =
    let c₀ = 2/3 ℚ.* c ℚ.+ 1/3 ℚ.* d
        d₀ = 1/3 ℚ.* c ℚ.+ 2/3 ℚ.* d
        c₀<d₀ : c₀ ℚ.< d₀
        c₀<d₀ = c-d-lemma c d c<d
        split = approxSplit
                  (capp f (fromℚ c₀))
                  (capp f (fromℚ d₀))
                  0ℝ
                  (f-inc (fromℚ c₀) (fromℚ d₀) (fromℚ-preserves-< c₀ d₀ c₀<d₀))
    in
    case split of λ
      { (inj₁ 0≤fd₀) →
          record
          { c = c
          ; d = d₀
          ; c<d = {!!}
          ; fc≤0 = fc≤0
          ; 0≤fd = 0≤fd₀
          }
        , record
          { c-mono = ℚ.≤-refl
          ; d-mono = {!!}
          ; d-c = {!!}
          }
    ; (inj₂ fc₀≤0) →
          record
          { c = c₀
          ; d = d
          ; c<d = {!!}
          ; fc≤0 = fc₀≤0
          ; 0≤fd = 0≤fd
          }
        , record
          { c-mono = {!!}
          ; d-mono = ℚ.≤-refl
          ; d-c = {!!}
          }
      }

  IVT :
    RecData →
    Σ ℝ (λ z → capp f z ≃ 0ℝ)
  IVT = {!!}
