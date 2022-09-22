{-# OPTIONS --allow-unsolved-metas #-}

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
cont.ω x^2-2 p = zero -- Definitely wrong!!!
cont.cauchy x^2-2 = {!!}
cont.ucont x^2-2 = {!!}  -- Impossible for now.

x^2-2-inc : strictly-increasing x^2-2
x^2-2-inc = λ x y (p , ½^p≤) →
    p  -- Should be ok in the interval [1;2].
  , {!!}  -- Impossible for now.

√2 : ℝ
√2 = proj₁ (IVT.Iteration.IVT x^2-2 x^2-2-inc 1ℚ 2ℚ {!!} {!!})

as : ℕ → ℚ
as = ℝ.as √2


-- We can compute as n simply by normalizing (C-c C-n):

-- as  5 computes to 107 / 81
-- as 10 computes to 27697 / 19683
-- as 20 would hang before the first optimization and took around 20s after
-- as 100 takes ca 1s now

-- as 100 takes ca 1s
-- as 200 takes ca 4s
-- as 300 takes ca 8s
-- as 400 takes ca 14s
-- as 500 takes ca 22s
-- as 600 takes ca 31s
-- as 700 takes ca 42s
-- as 800 takes ca 55s
-- Looks quadratic.
-- Which is the best we can expect!
