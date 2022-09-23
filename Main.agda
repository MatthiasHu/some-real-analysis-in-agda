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

-- Performance notes for execution of the compiled program:
-- n =  500 takes ca 0.5s
-- n = 1000 takes ca 2s
-- n = 1500 takes ca 5s
-- n = 2000 takes ca 9s
-- (This is ca 40x faster than evaluating by C-c C-n.)
-- These times are the same with and without erasure annotations ("@0" and "Erased").
