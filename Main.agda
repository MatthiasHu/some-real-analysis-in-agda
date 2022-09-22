{-# OPTIONS --guardedness #-}

module Main where

-- stdlib

open import IO
open import Data.Nat.Show as ℕ
open import Data.Rational.Show as ℚ
open import Function.Base using (case_of_)
open import Data.Maybe using (just; nothing)

-- ours

open import examples

main : Main
main = run (do
  putStrLn "Enter n:"
  str <- getLine
  case (ℕ.readMaybe 10 str) of λ
    { (just n) → putStrLn (ℚ.show (as n))
    ; nothing → putStrLn "Can't read this as a natural number."
    }
  )
