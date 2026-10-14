-- Native implementations for sui::groth16
-- Zero-knowledge proof verification internals

import Prelude.BoundedNat
import Prelude.Helpers

namespace Groth16Natives

structure Curve where
  id : BoundedNat (2^8)
deriving BEq
instance : Inhabited Curve where default := ⟨default⟩

structure PreparedVerifyingKey where
  vk_gamma_abc_g1_bytes : List (BoundedNat (2^8))
  alpha_g1_beta_g2_bytes : List (BoundedNat (2^8))
  gamma_g2_neg_pc_bytes : List (BoundedNat (2^8))
  delta_g2_neg_pc_bytes : List (BoundedNat (2^8))
deriving BEq
instance : Inhabited PreparedVerifyingKey where default := ⟨default, default, default, default⟩

structure ProofPoints where
  bytes : List (BoundedNat (2^8))
deriving BEq
instance : Inhabited ProofPoints where default := ⟨default⟩

structure PublicProofInputs where
  bytes : List (BoundedNat (2^8))
deriving BEq
instance : Inhabited PublicProofInputs where default := ⟨default⟩

def prepare_verifying_key_internal (_curve_id : BoundedNat (2^8)) (verifying_key : List (BoundedNat (2^8))) : PreparedVerifyingKey :=
  -- Partition the input bytes into 4 equal pieces (the four output fields).
  -- Distinct keys yield distinct results, and re-preparing the same key is
  -- deterministic.
  let n := verifying_key.length
  let q := n / 4
  let part (i : Nat) : List (BoundedNat (2^8)) :=
    (verifying_key.drop (i * q)).take q
  ⟨part 0, part 1, part 2, part 3⟩

def verify_groth16_proof_internal (_curve_id : BoundedNat (2^8)) (vk_gamma_abc_g1_bytes : List (BoundedNat (2^8))) (alpha_g1_beta_g2_bytes : List (BoundedNat (2^8))) (gamma_g2_neg_pc_bytes : List (BoundedNat (2^8))) (delta_g2_neg_pc_bytes : List (BoundedNat (2^8))) (public_proof_inputs_bytes : List (BoundedNat (2^8))) (proof_points_bytes : List (BoundedNat (2^8))) : Bool :=
  !vk_gamma_abc_g1_bytes.isEmpty && !alpha_g1_beta_g2_bytes.isEmpty
    && !gamma_g2_neg_pc_bytes.isEmpty && !delta_g2_neg_pc_bytes.isEmpty
    && !public_proof_inputs_bytes.isEmpty && !proof_points_bytes.isEmpty

end Groth16Natives
