open import Data.Nat
open import Relation.Binary.PropositionalEquality


data Pos : Set where
  One : Pos
  SZero : Pos → Pos
  SOne : Pos → Pos

private
  variable
    p q r : Pos
    n : ℕ

NatDouble : ℕ → ℕ
NatDouble zero = zero
NatDouble (suc n) = suc (suc (NatDouble n))

0<NatDouble : (n : ℕ) → 0 < n → 0 < NatDouble n
0<NatDouble (suc n) 0<n = s≤s z≤n

PosToNat : Pos → ℕ
PosToNat One = suc zero
PosToNat (SZero p) = NatDouble (PosToNat p)
PosToNat (SOne p) = suc (NatDouble (PosToNat p))

-- succ for Pos
PosS : Pos → Pos
PosS One = SZero One
PosS (SZero p) = SOne p
PosS (SOne p) = SZero (PosS p)

NatToPos : ℕ → Pos
NatToPos zero = One -- arbitrary
NatToPos (suc zero) = One
NatToPos (suc (suc n)) = PosS (NatToPos (suc n))

lemma1 : (n : ℕ) → 0 < n → NatToPos (NatDouble n) ≡ SZero (NatToPos n)
lemma1 (suc zero) 0<n = refl
lemma1 (suc (suc n)) 0<n = cong (λ x → PosS (PosS x)) (lemma1 (suc n) (s≤s z≤n))

lemma2 : (p : Pos) → 0 < PosToNat p
lemma2 One = s≤s z≤n
lemma2 (SZero p) = 0<NatDouble (PosToNat p) (lemma2 p)
lemma2 (SOne p) = s≤s z≤n

NatToPosToNatId : (p : Pos) → NatToPos (PosToNat p) ≡ p
NatToPosToNatId One = refl
NatToPosToNatId (SZero p) = trans (lemma1 (PosToNat p) (lemma2 p)) (cong SZero (NatToPosToNatId p))
NatToPosToNatId (SOne p) = {!!}
