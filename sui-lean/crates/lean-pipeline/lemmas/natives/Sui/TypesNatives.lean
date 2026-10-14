-- Native implementations for sui::types
-- Type introspection operations

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe

namespace Types

-- `sui::types::is_one_time_witness<T>(&witness)` returns true iff `T` is the
-- one-time witness type of its module. By Sui's OTW rule the witness struct's
-- simple name equals its module name upper-cased (`pool::POOL`,
-- `my_coin::MY_COIN`). The closed-universe `Universe.typeName` gives `T`'s
-- Move FQN `<64hex-addr>::<module>::<Type>`, so we decide it structurally:
-- split on `::` and check the type segment equals the module segment
-- upper-cased. Universe-generic (like the `type_name::*` natives) so the
-- renderer threads the caller's universe at the call site; `package::claim`
-- is the only caller. NOT a constant -- the value depends on `T`.
private def fqnIsOneTimeWitness (fqn : String) : Bool :=
  match fqn.splitOn "::" with
  | [_addr, moduleName, typeName] => typeName == moduleName.toUpper
  | _ => false

def is_one_time_witness {U : Type} [Universe U] [Repr U]
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [hc : HasCode U tv0]
    (_param0 : tv0) : Bool :=
  fqnIsOneTimeWitness (Universe.typeName hc.code)

end Types
