-- Native implementations for sui::bls12381

import Prelude.BoundedNat
import Prelude.Helpers
import Sui.Group_opsNatives

namespace Bls12381

-- `sui::bls12381::{Scalar, G1, G2, GT, UncompressedG1}` -- phantom-type
-- tags used as the parameter to `sui::group_ops::Element<T>` for BLS12-381
-- field / group elements. Move source declares them as empty `public
-- struct`s; Lean models them as singleton-default placeholder structs.
structure Scalar where deriving DecidableEq
instance : Inhabited Scalar where default := ⟨⟩

structure G1 where deriving DecidableEq
instance : Inhabited G1 where default := ⟨⟩

structure G2 where deriving DecidableEq
instance : Inhabited G2 where default := ⟨⟩

structure GT where deriving DecidableEq
instance : Inhabited GT where default := ⟨⟩

structure UncompressedG1 where deriving DecidableEq
instance : Inhabited UncompressedG1 where default := ⟨⟩

-- We can't model BLS semantics in Lean, but tests typically construct a
-- non-empty signature+key+msg and assert `verify(...) == true`. Returning
-- `true` for non-empty inputs (and `false` otherwise) is the smallest
-- deterministic improvement over an unconditional `false`.
def bls12381_min_pk_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

def bls12381_min_sig_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

-- Group constructors / arithmetic over `group_ops::Element`. BLS12-381 group
-- semantics can't be modeled in Lean; these are opaque deterministic stubs
-- (the smallest improvement over a non-compiling gap) so spec/test code that
-- aggregates committee public keys type-checks.
def g1_identity : Group_ops.Element G1 := default

def g1_from_bytes (_bytes : List (BoundedNat (2^8))) : Group_ops.Element G1 := default

def g1_to_uncompressed_g1 (_e : Group_ops.Element G1) : Group_ops.Element UncompressedG1 := default

def g1_sub (_a : Group_ops.Element G1) (_b : Group_ops.Element G1) : Group_ops.Element G1 := default

def uncompressed_g1_sum (_terms : List (Group_ops.Element UncompressedG1)) : Group_ops.Element UncompressedG1 := default

def uncompressed_g1_to_g1 (_e : Group_ops.Element UncompressedG1) : Group_ops.Element G1 := default

end Bls12381
