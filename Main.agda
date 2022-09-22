{-# OPTIONS --guardedness #-}

module Main where

-- stdlib

open import IO
open import Data.Rational.Show

-- ours

open import examples

main : Main
main = run (putStrLn (show (as 500)))
