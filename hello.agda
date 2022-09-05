{-
  Welcome to Agda! :-)

  If you are new to Agda, you could play The HoTT Game, a tutorial for learning
  Agda and homotopy type theory. You can start the game using the "Help" menu
  and then navigating to a file such as 1FundamentalGroup/Quest0.agda. You
  will also need to open the accompanying guide in your browser:
  https://thehottgameguide.readthedocs.io/

  This editor runs on agdapad.quasicoherent.io. Your Agda code is stored on
  this server and should be available when you revisit the same Agdapad session.
  However, absolutely no guarantees are made. You should make backups by
  downloading (see the clipboard icon in the lower right corner).

  C-c C-l          check file
  C-c C-SPC        check hole
  C-c C-,          display goal and context
  C-c C-c          split cases
  C-c C-r          fill in boilerplate from goal
  C-c C-d          display type of expression
  C-c C-v          evaluate expression (normally this is C-c C-n)
  C-c C-a          try to find proof automatically
  C-z              enable Vi keybindings
  C-x C-+          increase font size
  \bN \alpha \to   math symbols

  "C-c" means "<Ctrl key> + c". In case your browser is intercepting C-c,
  you can also use C-u. For pasting code into the Agdapad, see the clipboard
  icon in the lower right corner.

  In text mode, use <F10> to access the menu bar, not the mouse.
-}


data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ


-- Even

four = succ (succ (succ (succ zero)))

data Even : ℕ → Set where
  ezero : Even zero
  ess : ∀ {n} → Even n → Even (succ (succ n))

ex : Even four
ex = ess (ess ezero)

extract : {n : ℕ} → Even n → ℕ
extract ezero = zero
extract (ess x) = succ (extract x)


-- divMod

record Σ {A : Set} (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

_×_ : Set → Set → Set
A × B = Σ {A = A} (λ _ → B)

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then a else b = a
if false then a else b = b

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == succ b = false
succ a == zero = false
succ a == succ b = a == b

divMod : ℕ → ℕ → ℕ × ℕ
divMod b = λ a → go a zero
  where
  go : ℕ → ℕ → ℕ × ℕ
  go zero tmp = zero , tmp
  go (succ a) tmp =
    if succ tmp == b
    then (let p = go a zero
          in (succ (fst p)) , (snd p))
    else go a (succ tmp)


-- divMod as proof

data _<_ : ℕ → ℕ → Set where
  z<s : {n : ℕ} → zero < succ n
  s<s : {n m : ℕ} → n < m → succ n < succ m

_>_ : ℕ → ℕ → Set
a > b = b < a

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

cong :
  {A B : Set} →
  (f : A → B) →
  {a a' : A} →
  a ≡ a' → f a ≡ f a'
cong f refl = refl

trans :
  {A : Set} →
  {a a' a'' : A} →
  a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

_+_ : ℕ → ℕ → ℕ
-- _+_ = {!!}
a + zero = a
a + succ b = succ (a + b)
-- zero + b = zero
-- succ a + b = succ (a + b)

_*_ : ℕ → ℕ → ℕ
zero * b = zero
succ a * b = (a * b) + b

data _∐_ (A B : Set) : Set where
  inl : A → A ∐ B
  inr : B → A ∐ B

∐-rec :
  {A B C : Set} →
  (A → C) →
  (B → C) →
  A ∐ B → C
∐-rec f g (inl a) = f a
∐-rec f g (inr b) = g b

succDichotomyLemma :
  {r b : ℕ} →
  (r < b) →
  (succ r < b) ∐ (succ r ≡ b)
succDichotomyLemma (z<s {zero}) = inr refl
succDichotomyLemma (z<s {succ n}) = inl (s<s z<s)
succDichotomyLemma (s<s r<b) =
  ∐-rec
    (λ succn<m → inl (s<s succn<m))
    (λ succn≡m → inr (cong succ succn≡m))
    (succDichotomyLemma r<b)

divModThm :
  (b : ℕ) →
  (zero < b) →
  (a : ℕ) →
  Σ λ k → Σ λ r → (a ≡ ((k * b) + r)) × (r < b)
divModThm b 0<b zero = zero , (zero , (refl , 0<b))
divModThm b 0<b (succ a) =
  let (k , ( r , (a≡k*b+r , r<b) )) = divModThm b 0<b a
  in ∐-rec
       (λ succr<b → k , ((succ r) , (cong succ a≡k*b+r , succr<b)))
       (λ succr≡b → (succ k) , (zero ,
         ( trans
             {a' = succ ((k * b) + r)}
             (cong succ a≡k*b+r)
             (cong ((k * b) +_) succr≡b)
         , 0<b)))
       (succDichotomyLemma r<b)

{-
divModThm b 0<b zero = zero , (zero , (refl , 0<b))
divModThm b 0<b (succ a) =
  let k , (r , (a≡k*b+r , r<b)) = divModThm b 0<b a
  in ∐-rec
       (λ succr<b →
         k ,
         (succ r ,
         (cong succ a≡k*b+r ,
         succr<b)))
       (λ succr≡b →
         succ k ,
         (zero ,
         (trans (cong succ a≡k*b+r)
                (cong ((k * b) +_) succr≡b) ,
         0<b)))
       (succDichotomyLemma r<b)
-}
