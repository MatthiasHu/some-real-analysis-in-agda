{-# OPTIONS --guardedness #-}

module Main where

open import IO

open import examples

main : Main
main = run (putStrLn "Hello, stdlib!")
