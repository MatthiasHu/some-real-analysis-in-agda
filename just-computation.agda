open import Data.Nat as ℕ using (ℕ; suc)
import Data.Integer as ℤ
open import Data.Rational
-- open import Function.Base using (case_of_)
open import Data.Bool using (true; false)
open import Relation.Nullary
open import Relation.Nullary.Decidable


case_of_ : {A B : Set} →  A → (A → B) → B
case x of f = f x
{-# NOINLINE case_of_ #-}


1/2 = ½
1/3 = ℤ.+ 1 / 3
2/3 = ℤ.+ 2 / 3
1/4 = ℤ.+ 1 / 4
3/4 = ℤ.+ 3 / 4
2ℚ = ℤ.+ 2 / 1

_^_ : ℚ → ℕ → ℚ
a ^ ℕ.zero = 1ℚ
a ^ ℕ.suc n = a * (a ^ n)

f : ℚ → ℚ
f a = a * a - 2ℚ


as : ℕ → ℚ
as ℕ.zero = 1ℚ
as (ℕ.suc n) =
  case as n of λ left →
  case left + (½ ^ suc n) of λ mid →
  case 0ℚ <? f mid of λ
  { (no ¬p) → mid
  ; (yes p) → left
  }


bs : ℕ → ℚ
bs ℕ.zero = 1ℚ
bs (ℕ.suc n) = 2/3 * bs n



open import Agda.Builtin.Strict

co = case_of_

syntax co x (λ a → body) = let' a be x in' body

cs : ℕ → ℕ
cs ℕ.zero = 1
cs (suc n) =
  case cs n of (λ { ℕ.zero → 0 ; a → a ℕ.+ a })
--  let' a be cs n in' (a ℕ.+ a)  -- fast.
--  primForce (cs n) (λ a → a ℕ.+ a)  -- fast.
--  a ℕ.+ a where a = cs n  -- slow.
--  case cs n of (λ a → a ℕ.+ a)  -- fast.
--  let a = cs n in a ℕ.+ a   -- slow.

