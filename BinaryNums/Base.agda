open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

module BinaryNums.Base where

data Bin : ℕ → Set where
  zero : Bin 0
  _,0 : ∀ {n} → Bin n → Bin (0 + n * 2)
  _,1 : ∀ {n} → Bin n → Bin (1 + n * 2)

sucᵇ : ∀ {n} → Bin n → Bin (suc n)
sucᵇ zero   = zero ,1
sucᵇ (b ,0) = b ,1
sucᵇ (b ,1) = (sucᵇ b) ,0

natToBin : ∀ n → Bin n
natToBin 0 = zero
natToBin (suc n) = sucᵇ (natToBin n)
