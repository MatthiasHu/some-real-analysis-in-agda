
module continuous where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Rational as ℚ using (ℚ; ½)
import Data.Rational.Properties as ℚ
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import real as ℝ using (ℝ; Cauchy; ½^sucp+½^sucp≡½^p)


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
    -- ...

insert-lemma : (a b c : ℚ) → a ℚ.- c ≡ (a ℚ.- b) ℚ.+ (b ℚ.- c)
insert-lemma = {!!}

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
  