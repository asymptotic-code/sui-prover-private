-- Native implementations for sui::ecdsa_k1
-- Secp256k1 elliptic curve operations

import Prelude.BoundedNat
import Prelude.Helpers

namespace Ecdsa_k1Natives

structure KeyPair where
  private_key : List (BoundedNat (2^8))
  public_key : List (BoundedNat (2^8))
deriving BEq
instance : Inhabited KeyPair where default := ⟨default, default⟩

def public_key (self : KeyPair) : List (BoundedNat (2^8)) := self.public_key
def private_key (self : KeyPair) : List (BoundedNat (2^8)) := self.private_key
def secp256k1_ecrecover (_signature : List (BoundedNat (2^8))) (_msg : List (BoundedNat (2^8))) (_hash : BoundedNat (2^8)) : List (BoundedNat (2^8)) := []
def decompress_pubkey (_pubkey : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) := []
def secp256k1_keypair_from_seed (_seed : List (BoundedNat (2^8))) : KeyPair := default
def secp256k1_sign (_private_key : List (BoundedNat (2^8))) (_msg : List (BoundedNat (2^8))) (_hash : BoundedNat (2^8)) (_recoverable : Bool) : List (BoundedNat (2^8)) := []

def secp256k1_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) (_hash : BoundedNat (2^8)) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

end Ecdsa_k1Natives
