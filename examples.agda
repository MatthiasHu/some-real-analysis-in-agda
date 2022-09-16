module examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ
open import Data.Rational as ℚ using (ℚ; ½; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ
import Data.Integer as ℤ
open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import Function.Base using (case_of_)

open import Algebra.Bundles using (module Ring)
open import Algebra.Properties.Semiring.Exp (Ring.semiring ℚ.+-*-ring)

open import preliminaries.on-rationals
open import preliminaries.convex-combination
open import real as ℝ using (ℝ; Cauchy; 0ℝ; _≃_; fromℚ; approxSplit; fromℚ-preserves-<)
open import continuous


x^2-2 : cont
cont.h x^2-2 a p = a ^ 2 ℚ.- 2ℚ
cont.α x^2-2 p = 0
cont.ω x^2-2 = {!!}
cont.cauchy x^2-2 = {!!}
cont.ucont x^2-2 = {!!}  -- Impossible for now.

x^2-2-inc : strictly-increasing x^2-2
x^2-2-inc = {!!}

√2 : ℝ
√2 = proj₁ (IVT.Iteration.IVT x^2-2 x^2-2-inc 1ℚ 2ℚ {!!} {!!})

as : ℕ → ℚ
as = ℝ.as √2

-- as  5 computes to 107 / 81
-- as 10 computes to 27697 / 19683
-- as 20 would hang before optimization and takes around 20s now
