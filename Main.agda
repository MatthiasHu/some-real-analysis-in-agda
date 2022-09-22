{-# OPTIONS --guardedness #-}

module Main where

open import IO

main : Main
main = run (putStrLn "Hello, stdlib!")
