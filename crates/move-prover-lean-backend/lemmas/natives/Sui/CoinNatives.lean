-- Native implementations for sui::coin

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import Prelude.ProgramState
import Sui.Balance
import Sui.BalanceNatives
import Sui.Object
import Sui.Tx_context

namespace Coin

structure Coin (tv0 : Type) where
  id : Object.UID
  balance : Balance.Balance tv0
deriving BEq
instance [Inhabited tv0] : Inhabited (Coin tv0) where default := ⟨default, default⟩

structure TreasuryCap (tv0 : Type) where
  id : Object.UID
  total_supply : Balance.Supply tv0
deriving BEq
instance [Inhabited tv0] : Inhabited (TreasuryCap tv0) where default := ⟨default, default⟩

def value (tv0 : Type) [BEq tv0] [Inhabited tv0] (self : Coin tv0) : BoundedNat (2^64) :=
  Balance.value tv0 self.balance

-- Burn destroys a Coin and decrements the cap's total supply by the coin's value.
-- Aborts if the supply would underflow.
def burn (tv0 : Type) [BEq tv0] [Inhabited tv0] (cap : TreasuryCap tv0) (c : Coin tv0) : (BoundedNat (2^64) × TreasuryCap tv0) :=
  let v := c.balance.value
  let new_supply : Balance.Supply tv0 := { value := cap.total_supply.value - v }
  let new_cap : TreasuryCap tv0 := { cap with total_supply := new_supply }
  (v, new_cap)

def burn.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (cap : TreasuryCap tv0) (c : Coin tv0) : Option MoveAbort :=
  if BoundedNat.sub_underflows cap.total_supply.value c.balance.value then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

-- Take splits `value` off a Balance into a fresh Coin.
-- Aborts if the balance would underflow.
def take (tv0 : Type) [BEq tv0] [Inhabited tv0] (balance : Balance.Balance tv0) (value : BoundedNat (2^64)) (ctx : Tx_context.TxContext) : (Coin tv0 × Balance.Balance tv0 × Tx_context.TxContext) :=
  let new_balance : Balance.Balance tv0 := { value := balance.value - value }
  let new_coin : Coin tv0 := { id := default, balance := { value := value } }
  (new_coin, new_balance, ctx)

def take.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (balance : Balance.Balance tv0) (value : BoundedNat (2^64)) (_ctx : Tx_context.TxContext) : Option MoveAbort :=
  if BoundedNat.sub_underflows balance.value value then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

-- Split takes `split_amount` off a Coin, returning the remaining Coin and a new Coin.
def split (tv0 : Type) [BEq tv0] [Inhabited tv0] (self : Coin tv0) (split_amount : BoundedNat (2^64)) (ctx : Tx_context.TxContext) : (Coin tv0 × Coin tv0 × Tx_context.TxContext) :=
  let new_self_balance : Balance.Balance tv0 := { value := self.balance.value - split_amount }
  let updated_self : Coin tv0 := { self with balance := new_self_balance }
  let new_coin : Coin tv0 := { id := default, balance := { value := split_amount } }
  (updated_self, new_coin, ctx)

def split.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (self : Coin tv0) (split_amount : BoundedNat (2^64)) (_ctx : Tx_context.TxContext) : Option MoveAbort :=
  if BoundedNat.sub_underflows self.balance.value split_amount then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def into_balance (tv0 : Type) [BEq tv0] [Inhabited tv0] (coin : Coin tv0) : Balance.Balance tv0 :=
  coin.balance

-- Mint creates a fresh Coin of the given value, increments the cap's total supply.
-- Aborts if the supply would overflow.
def mint (tv0 : Type) [BEq tv0] [Inhabited tv0] (cap : TreasuryCap tv0) (value : BoundedNat (2^64)) (ctx : Tx_context.TxContext) : (Coin tv0 × TreasuryCap tv0 × Tx_context.TxContext) :=
  let new_supply : Balance.Supply tv0 := { value := cap.total_supply.value + value }
  let new_cap : TreasuryCap tv0 := { cap with total_supply := new_supply }
  let new_coin : Coin tv0 := { id := default, balance := { value := value } }
  (new_coin, new_cap, ctx)

def mint.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (cap : TreasuryCap tv0) (value : BoundedNat (2^64)) (_ctx : Tx_context.TxContext) : Option MoveAbort :=
  if BoundedNat.add_overflows cap.total_supply.value value then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def total_supply (tv0 : Type) [BEq tv0] [Inhabited tv0] (cap : TreasuryCap tv0) : BoundedNat (2^64) :=
  cap.total_supply.value

end Coin
