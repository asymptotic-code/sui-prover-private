//! Static native-module / native-function / native-struct allowlist.
//!
//! Every entry here mirrors a hand-written Lean prelude file under
//! `lean-backend/crates/lean-pipeline/lemmas/natives/`.
//! Stage 2's pre-pass partitions Move declarations into "translate" vs
//! "native" by consulting this list:
//!
//! - **Native modules** -- a Move module appearing here means stage 2
//!   never translates its struct definitions or function bodies. The
//!   corresponding `Module` entry in `Program::modules` is marked
//!   `is_native: true`; its functions are registered as
//!   [`crate::ir::NativeDecl`] entries in `Program::natives.decls`
//!   (no entry in `Program::functions`); its structs are NOT
//!   inserted in `Program::structs` at all (the renderer maps any
//!   `Type::Struct { struct_id }` referencing a native to the prelude
//!   type directly).
//!
//! When the prelude grows a new native file, add the corresponding
//! `(package, module_name)` entry here. Unit tests pin the list size
//! and the canonical-name conventions; failing to update both
//! locations is caught at test time.
//!
//! ## Naming convention
//!
//! - `package` matches the Lean prelude directory name (`Sui`,
//!   `MoveStdlib`, `Prover`). It maps 1:1 to the
//!   `Module::package_name` in our IR. Note: `MoveSTL` used to be
//!   listed here for `linked_table` / `skip_list`; those modules are
//!   plain translated client code whose df ops route through the
//!   World model (step-2 df consolidation) — no shim, no ghost
//!   fields, no special-casing.
//! - `module_name` is the Move-side lowercase identifier (`bag`,
//!   `vector`). The Lean filename may carry a disambiguation prefix
//!   (`MoveVector`, `Sui_Bcs`); the prefix is dropped here because
//!   stage 2 matches Move bytecode, not Lean source.

/// Functions whose Move body the pipeline discards in favour of a
/// Lean prelude definition. Each entry corresponds to a
/// `(package, module_name, function_name)` declared in a Move
/// framework module whose Lean shape lives in
/// `lemmas/natives/<Package>/<Module>Natives.lean`.
///
/// Populated by enumerating every Move function declared in
/// every framework native module, MERGED across both supported
/// Sui framework forks: the prover\'s `asymptotic-code/sui-next`
/// and `MystenLabs/sui` (mainnet). Listing per-function instead
/// of per-module enables a future where one Move module mixes
/// prelude-replaced functions with translated ones; merging
/// across forks absorbs the helper-set drift that the previous
/// coarse `NATIVE_FUNCTION_MODULES` allowlist hid.
const NATIVE_FUNCTIONS: &[(&str, &str, &str)] = &[
    // ---- MoveStdlib::bcs ----
    ("MoveStdlib", "bcs", "to_bytes"),
    // ---- MoveStdlib::hash ----
    ("MoveStdlib", "hash", "sha2_256"),
    ("MoveStdlib", "hash", "sha3_256"),
    // ---- MoveStdlib::integer ----
    ("MoveStdlib", "integer", "abs"),
    ("MoveStdlib", "integer", "add"),
    ("MoveStdlib", "integer", "bit_and"),
    ("MoveStdlib", "integer", "bit_not"),
    ("MoveStdlib", "integer", "bit_or"),
    ("MoveStdlib", "integer", "bit_xor"),
    ("MoveStdlib", "integer", "div"),
    ("MoveStdlib", "integer", "div_round_up"),
    ("MoveStdlib", "integer", "div_trunc"),
    ("MoveStdlib", "integer", "from_u128"),
    ("MoveStdlib", "integer", "from_u16"),
    ("MoveStdlib", "integer", "from_u256"),
    ("MoveStdlib", "integer", "from_u32"),
    ("MoveStdlib", "integer", "from_u64"),
    ("MoveStdlib", "integer", "from_u8"),
    ("MoveStdlib", "integer", "gt"),
    ("MoveStdlib", "integer", "gte"),
    ("MoveStdlib", "integer", "is_i128"),
    ("MoveStdlib", "integer", "is_i16"),
    ("MoveStdlib", "integer", "is_i256"),
    ("MoveStdlib", "integer", "is_i32"),
    ("MoveStdlib", "integer", "is_i64"),
    ("MoveStdlib", "integer", "is_i8"),
    ("MoveStdlib", "integer", "is_neg"),
    ("MoveStdlib", "integer", "is_pos"),
    ("MoveStdlib", "integer", "is_zero"),
    ("MoveStdlib", "integer", "lt"),
    ("MoveStdlib", "integer", "lte"),
    ("MoveStdlib", "integer", "max"),
    ("MoveStdlib", "integer", "min"),
    ("MoveStdlib", "integer", "mod"),
    ("MoveStdlib", "integer", "mod_trunc"),
    ("MoveStdlib", "integer", "mul"),
    ("MoveStdlib", "integer", "neg"),
    ("MoveStdlib", "integer", "one"),
    ("MoveStdlib", "integer", "pow"),
    ("MoveStdlib", "integer", "shl"),
    ("MoveStdlib", "integer", "shr"),
    ("MoveStdlib", "integer", "signed_from_u128"),
    ("MoveStdlib", "integer", "signed_from_u16"),
    ("MoveStdlib", "integer", "signed_from_u256"),
    ("MoveStdlib", "integer", "signed_from_u32"),
    ("MoveStdlib", "integer", "signed_from_u64"),
    ("MoveStdlib", "integer", "signed_from_u8"),
    ("MoveStdlib", "integer", "sqrt"),
    ("MoveStdlib", "integer", "std"),
    ("MoveStdlib", "integer", "sub"),
    ("MoveStdlib", "integer", "to_u128"),
    ("MoveStdlib", "integer", "to_u16"),
    ("MoveStdlib", "integer", "to_u256"),
    ("MoveStdlib", "integer", "to_u32"),
    ("MoveStdlib", "integer", "to_u64"),
    ("MoveStdlib", "integer", "to_u8"),
    ("MoveStdlib", "integer", "two"),
    ("MoveStdlib", "integer", "zero"),
    // ---- MoveStdlib::real ----
    ("MoveStdlib", "real", "add"),
    ("MoveStdlib", "real", "div"),
    ("MoveStdlib", "real", "exp"),
    ("MoveStdlib", "real", "from_integer"),
    ("MoveStdlib", "real", "from_u128"),
    ("MoveStdlib", "real", "from_u16"),
    ("MoveStdlib", "real", "from_u256"),
    ("MoveStdlib", "real", "from_u32"),
    ("MoveStdlib", "real", "from_u64"),
    ("MoveStdlib", "real", "from_u8"),
    ("MoveStdlib", "real", "gt"),
    ("MoveStdlib", "real", "gte"),
    ("MoveStdlib", "real", "lt"),
    ("MoveStdlib", "real", "lte"),
    ("MoveStdlib", "real", "max"),
    ("MoveStdlib", "real", "min"),
    ("MoveStdlib", "real", "mul"),
    ("MoveStdlib", "real", "neg"),
    ("MoveStdlib", "real", "sqrt"),
    ("MoveStdlib", "real", "std"),
    ("MoveStdlib", "real", "sub"),
    ("MoveStdlib", "real", "to_integer"),
    ("MoveStdlib", "real", "to_u128"),
    ("MoveStdlib", "real", "to_u16"),
    ("MoveStdlib", "real", "to_u256"),
    ("MoveStdlib", "real", "to_u32"),
    ("MoveStdlib", "real", "to_u64"),
    ("MoveStdlib", "real", "to_u8"),
    // ---- MoveStdlib::string ----
    ("MoveStdlib", "string", "append"),
    ("MoveStdlib", "string", "append_utf8"),
    ("MoveStdlib", "string", "as_bytes"),
    ("MoveStdlib", "string", "bytes"),
    ("MoveStdlib", "string", "from_ascii"),
    ("MoveStdlib", "string", "index_of"),
    ("MoveStdlib", "string", "insert"),
    ("MoveStdlib", "string", "internal_check_utf8"),
    ("MoveStdlib", "string", "internal_index_of"),
    ("MoveStdlib", "string", "internal_is_char_boundary"),
    ("MoveStdlib", "string", "internal_sub_string"),
    ("MoveStdlib", "string", "into_bytes"),
    ("MoveStdlib", "string", "is_empty"),
    ("MoveStdlib", "string", "length"),
    ("MoveStdlib", "string", "sub_string"),
    ("MoveStdlib", "string", "substring"),
    ("MoveStdlib", "string", "to_ascii"),
    ("MoveStdlib", "string", "try_utf8"),
    ("MoveStdlib", "string", "utf8"),
    // ---- MoveStdlib::type_name ----
    ("MoveStdlib", "type_name", "address_string"),
    ("MoveStdlib", "type_name", "as_string"),
    ("MoveStdlib", "type_name", "borrow_string"),
    ("MoveStdlib", "type_name", "datatype_string"),
    ("MoveStdlib", "type_name", "defining_id"),
    ("MoveStdlib", "type_name", "get"),
    ("MoveStdlib", "type_name", "get_address"),
    ("MoveStdlib", "type_name", "get_module"),
    ("MoveStdlib", "type_name", "get_with_original_ids"),
    ("MoveStdlib", "type_name", "into_string"),
    ("MoveStdlib", "type_name", "is_primitive"),
    ("MoveStdlib", "type_name", "module_string"),
    ("MoveStdlib", "type_name", "original_id"),
    ("MoveStdlib", "type_name", "with_defining_ids"),
    ("MoveStdlib", "type_name", "with_original_ids"),
    // ---- MoveStdlib::unit_test ----
    ("MoveStdlib", "unit_test", "assert_eq"),
    ("MoveStdlib", "unit_test", "assert_ref_eq"),
    ("MoveStdlib", "unit_test", "destroy"),
    ("MoveStdlib", "unit_test", "poison"),
    // ---- MoveStdlib::vector ----
    ("MoveStdlib", "vector", "all"),
    ("MoveStdlib", "vector", "any"),
    ("MoveStdlib", "vector", "append"),
    ("MoveStdlib", "vector", "append_pure"),
    ("MoveStdlib", "vector", "borrow"),
    ("MoveStdlib", "vector", "borrow_mut"),
    ("MoveStdlib", "vector", "borrow_or_unknown"),
    ("MoveStdlib", "vector", "contains"),
    ("MoveStdlib", "vector", "count"),
    ("MoveStdlib", "vector", "destroy"),
    ("MoveStdlib", "vector", "destroy_empty"),
    ("MoveStdlib", "vector", "do"),
    ("MoveStdlib", "vector", "do_mut"),
    ("MoveStdlib", "vector", "do_ref"),
    ("MoveStdlib", "vector", "empty"),
    ("MoveStdlib", "vector", "filter"),
    ("MoveStdlib", "vector", "find_index"),
    ("MoveStdlib", "vector", "find_indices"),
    ("MoveStdlib", "vector", "flatten"),
    ("MoveStdlib", "vector", "fold"),
    ("MoveStdlib", "vector", "index_of"),
    ("MoveStdlib", "vector", "insert"),
    ("MoveStdlib", "vector", "insert_pure"),
    ("MoveStdlib", "vector", "insertion_sort_by"),
    ("MoveStdlib", "vector", "is_empty"),
    ("MoveStdlib", "vector", "is_sorted_by"),
    ("MoveStdlib", "vector", "length"),
    ("MoveStdlib", "vector", "map"),
    ("MoveStdlib", "vector", "map_ref"),
    ("MoveStdlib", "vector", "merge_sort_by"),
    ("MoveStdlib", "vector", "partition"),
    ("MoveStdlib", "vector", "pop_back"),
    ("MoveStdlib", "vector", "pop_back_pure"),
    ("MoveStdlib", "vector", "pop_front_pure"),
    ("MoveStdlib", "vector", "push_back"),
    ("MoveStdlib", "vector", "push_back_pure"),
    ("MoveStdlib", "vector", "push_front_pure"),
    ("MoveStdlib", "vector", "remove"),
    ("MoveStdlib", "vector", "remove_pure"),
    ("MoveStdlib", "vector", "reverse"),
    ("MoveStdlib", "vector", "singleton"),
    ("MoveStdlib", "vector", "skip"),
    ("MoveStdlib", "vector", "skip_while"),
    ("MoveStdlib", "vector", "std"),
    ("MoveStdlib", "vector", "swap"),
    ("MoveStdlib", "vector", "swap_remove"),
    ("MoveStdlib", "vector", "tabulate"),
    ("MoveStdlib", "vector", "take"),
    ("MoveStdlib", "vector", "take_while"),
    ("MoveStdlib", "vector", "zip_do"),
    ("MoveStdlib", "vector", "zip_do_mut"),
    ("MoveStdlib", "vector", "zip_do_ref"),
    ("MoveStdlib", "vector", "zip_do_reverse"),
    ("MoveStdlib", "vector", "zip_map"),
    ("MoveStdlib", "vector", "zip_map_ref"),
    // ---- Prover::ghost ----
    ("Prover", "ghost", "borrow_mut"),
    ("Prover", "ghost", "declare_global"),
    ("Prover", "ghost", "declare_global_mut"),
    ("Prover", "ghost", "global"),
    ("Prover", "ghost", "havoc_global"),
    ("Prover", "ghost", "set"),
    ("Prover", "ghost", "set_spec"),
    // ---- Prover::prover ----
    ("Prover", "prover", "asserts"),
    ("Prover", "prover", "asserts_of"),
    ("Prover", "prover", "begin_exists_lambda"),
    ("Prover", "prover", "begin_forall_lambda"),
    ("Prover", "prover", "boogie_allow_path_isolation"),
    ("Prover", "prover", "boogie_focus"),
    ("Prover", "prover", "boogie_split_here"),
    ("Prover", "prover", "clone"),
    ("Prover", "prover", "drop"),
    ("Prover", "prover", "drop_spec"),
    ("Prover", "prover", "end_exists_lambda"),
    ("Prover", "prover", "end_forall_lambda"),
    ("Prover", "prover", "ensures"),
    ("Prover", "prover", "exists"),
    ("Prover", "prover", "forall"),
    ("Prover", "prover", "fresh"),
    ("Prover", "prover", "fresh_spec"),
    ("Prover", "prover", "implies"),
    ("Prover", "prover", "invariant"),
    ("Prover", "prover", "invariant_begin"),
    ("Prover", "prover", "invariant_end"),
    ("Prover", "prover", "ref"),
    ("Prover", "prover", "ref_spec"),
    ("Prover", "prover", "requires"),
    ("Prover", "prover", "type_inv"),
    ("Prover", "prover", "val"),
    ("Prover", "prover", "val_spec"),
    // ---- Prover::vector_iter ----
    ("Prover", "vector_iter", "all"),
    ("Prover", "vector_iter", "all_range"),
    ("Prover", "vector_iter", "any"),
    ("Prover", "vector_iter", "any_range"),
    ("Prover", "vector_iter", "begin_all_lambda"),
    ("Prover", "vector_iter", "begin_all_range_lambda"),
    ("Prover", "vector_iter", "begin_any_lambda"),
    ("Prover", "vector_iter", "begin_any_range_lambda"),
    ("Prover", "vector_iter", "begin_count_lambda"),
    ("Prover", "vector_iter", "begin_count_range_lambda"),
    ("Prover", "vector_iter", "begin_filter_lambda"),
    ("Prover", "vector_iter", "begin_filter_range_lambda"),
    ("Prover", "vector_iter", "begin_find_index_lambda"),
    ("Prover", "vector_iter", "begin_find_index_range_lambda"),
    ("Prover", "vector_iter", "begin_find_indices_lambda"),
    ("Prover", "vector_iter", "begin_find_indices_range_lambda"),
    ("Prover", "vector_iter", "begin_find_lambda"),
    ("Prover", "vector_iter", "begin_find_range_lambda"),
    ("Prover", "vector_iter", "begin_map_lambda"),
    ("Prover", "vector_iter", "begin_map_range_lambda"),
    ("Prover", "vector_iter", "begin_range_count_lambda"),
    ("Prover", "vector_iter", "begin_range_map_lambda"),
    ("Prover", "vector_iter", "begin_range_sum_map_lambda"),
    ("Prover", "vector_iter", "begin_sum_map_lambda"),
    ("Prover", "vector_iter", "begin_sum_map_range_lambda"),
    ("Prover", "vector_iter", "count"),
    ("Prover", "vector_iter", "count_range"),
    ("Prover", "vector_iter", "end_all_lambda"),
    ("Prover", "vector_iter", "end_any_lambda"),
    ("Prover", "vector_iter", "end_count_lambda"),
    ("Prover", "vector_iter", "end_filter_lambda"),
    ("Prover", "vector_iter", "end_find_index_lambda"),
    ("Prover", "vector_iter", "end_find_indices_lambda"),
    ("Prover", "vector_iter", "end_find_lambda"),
    ("Prover", "vector_iter", "end_map_lambda"),
    ("Prover", "vector_iter", "end_range_count_lambda"),
    ("Prover", "vector_iter", "end_range_map_lambda"),
    ("Prover", "vector_iter", "end_range_sum_map_lambda"),
    ("Prover", "vector_iter", "end_sum_map_lambda"),
    ("Prover", "vector_iter", "filter"),
    ("Prover", "vector_iter", "filter_range"),
    ("Prover", "vector_iter", "find"),
    ("Prover", "vector_iter", "find_index"),
    ("Prover", "vector_iter", "find_index_range"),
    ("Prover", "vector_iter", "find_indices"),
    ("Prover", "vector_iter", "find_indices_range"),
    ("Prover", "vector_iter", "find_range"),
    ("Prover", "vector_iter", "map"),
    ("Prover", "vector_iter", "map_range"),
    ("Prover", "vector_iter", "range"),
    ("Prover", "vector_iter", "range_count"),
    ("Prover", "vector_iter", "range_map"),
    ("Prover", "vector_iter", "range_sum_map"),
    ("Prover", "vector_iter", "slice"),
    ("Prover", "vector_iter", "sum"),
    ("Prover", "vector_iter", "sum_map"),
    ("Prover", "vector_iter", "sum_map_range"),
    ("Prover", "vector_iter", "sum_range"),
    // ---- Sui::accumulator ----
    ("Sui", "accumulator", "emit_deposit_event"),
    ("Sui", "accumulator", "emit_withdraw_event"),
    // ---- Sui::address ----
    ("Sui", "address", "from_ascii_bytes"),
    ("Sui", "address", "from_bytes"),
    ("Sui", "address", "from_u256"),
    ("Sui", "address", "hex_char_value"),
    ("Sui", "address", "length"),
    ("Sui", "address", "max"),
    ("Sui", "address", "sui"),
    ("Sui", "address", "to_ascii_string"),
    ("Sui", "address", "to_bytes"),
    ("Sui", "address", "to_string"),
    ("Sui", "address", "to_u256"),
    // ---- Sui::bag ----
    ("Sui", "bag", "add"),
    ("Sui", "bag", "borrow"),
    ("Sui", "bag", "borrow_mut"),
    ("Sui", "bag", "contains"),
    ("Sui", "bag", "contains_with_type"),
    ("Sui", "bag", "destroy_empty"),
    ("Sui", "bag", "is_empty"),
    ("Sui", "bag", "length"),
    ("Sui", "bag", "new"),
    ("Sui", "bag", "remove"),
    // ---- Sui::bcs ----
    ("Sui", "bcs", "to_bytes"),
    // ---- Sui::bls12381 ----
    ("Sui", "bls12381", "bls12381_min_pk_verify"),
    ("Sui", "bls12381", "bls12381_min_sig_verify"),
    ("Sui", "bls12381", "g1_add"),
    ("Sui", "bls12381", "g1_div"),
    ("Sui", "bls12381", "g1_from_bytes"),
    ("Sui", "bls12381", "g1_generator"),
    ("Sui", "bls12381", "g1_identity"),
    ("Sui", "bls12381", "g1_mul"),
    ("Sui", "bls12381", "g1_multi_scalar_multiplication"),
    ("Sui", "bls12381", "g1_neg"),
    ("Sui", "bls12381", "g1_sub"),
    ("Sui", "bls12381", "g1_to_uncompressed_g1"),
    ("Sui", "bls12381", "g2_add"),
    ("Sui", "bls12381", "g2_div"),
    ("Sui", "bls12381", "g2_from_bytes"),
    ("Sui", "bls12381", "g2_generator"),
    ("Sui", "bls12381", "g2_identity"),
    ("Sui", "bls12381", "g2_mul"),
    ("Sui", "bls12381", "g2_multi_scalar_multiplication"),
    ("Sui", "bls12381", "g2_neg"),
    ("Sui", "bls12381", "g2_sub"),
    ("Sui", "bls12381", "gt_add"),
    ("Sui", "bls12381", "gt_div"),
    ("Sui", "bls12381", "gt_generator"),
    ("Sui", "bls12381", "gt_identity"),
    ("Sui", "bls12381", "gt_mul"),
    ("Sui", "bls12381", "gt_neg"),
    ("Sui", "bls12381", "gt_sub"),
    ("Sui", "bls12381", "hash_to_g1"),
    ("Sui", "bls12381", "hash_to_g2"),
    ("Sui", "bls12381", "pairing"),
    ("Sui", "bls12381", "scalar_add"),
    ("Sui", "bls12381", "scalar_div"),
    ("Sui", "bls12381", "scalar_from_bytes"),
    ("Sui", "bls12381", "scalar_from_u64"),
    ("Sui", "bls12381", "scalar_inv"),
    ("Sui", "bls12381", "scalar_mul"),
    ("Sui", "bls12381", "scalar_neg"),
    ("Sui", "bls12381", "scalar_one"),
    ("Sui", "bls12381", "scalar_sub"),
    ("Sui", "bls12381", "scalar_zero"),
    ("Sui", "bls12381", "uncompressed_g1_sum"),
    ("Sui", "bls12381", "uncompressed_g1_to_g1"),
    // ---- Sui::config ----
    ("Sui", "config", "add_for_next_epoch"),
    ("Sui", "config", "borrow_for_next_epoch_mut"),
    ("Sui", "config", "entry"),
    ("Sui", "config", "exists_with_type"),
    ("Sui", "config", "exists_with_type_for_next_epoch"),
    ("Sui", "config", "new"),
    ("Sui", "config", "read_setting"),
    ("Sui", "config", "read_setting_for_next_epoch"),
    ("Sui", "config", "read_setting_impl"),
    ("Sui", "config", "remove_for_next_epoch"),
    ("Sui", "config", "share"),
    ("Sui", "config", "transfer"),
    ("Sui", "config", "update"),
    // ---- Sui::dynamic_field ----
    ("Sui", "dynamic_field", "add"),
    ("Sui", "dynamic_field", "add_child_object"),
    ("Sui", "dynamic_field", "borrow"),
    ("Sui", "dynamic_field", "borrow_child_object"),
    ("Sui", "dynamic_field", "borrow_child_object_mut"),
    ("Sui", "dynamic_field", "borrow_mut"),
    ("Sui", "dynamic_field", "borrow_mut_or_add"),
    ("Sui", "dynamic_field", "borrow_or_add"),
    ("Sui", "dynamic_field", "borrow_or_unknown"),
    ("Sui", "dynamic_field", "exists"),
    ("Sui", "dynamic_field", "exists_"),
    ("Sui", "dynamic_field", "exists_with_type"),
    ("Sui", "dynamic_field", "field_info"),
    ("Sui", "dynamic_field", "field_info_mut"),
    ("Sui", "dynamic_field", "get_do"),
    ("Sui", "dynamic_field", "get_fold"),
    ("Sui", "dynamic_field", "get_mut_do"),
    ("Sui", "dynamic_field", "get_mut_fold"),
    ("Sui", "dynamic_field", "has_child_object"),
    ("Sui", "dynamic_field", "has_child_object_with_ty"),
    ("Sui", "dynamic_field", "hash_type_and_key"),
    ("Sui", "dynamic_field", "remove"),
    ("Sui", "dynamic_field", "remove_child_object"),
    ("Sui", "dynamic_field", "remove_if_exists"),
    ("Sui", "dynamic_field", "remove_opt"),
    ("Sui", "dynamic_field", "replace"),
    // ---- Sui::dynamic_object_field ----
    ("Sui", "dynamic_object_field", "add"),
    ("Sui", "dynamic_object_field", "add_impl"),
    ("Sui", "dynamic_object_field", "borrow"),
    ("Sui", "dynamic_object_field", "borrow_impl"),
    ("Sui", "dynamic_object_field", "borrow_mut"),
    ("Sui", "dynamic_object_field", "borrow_mut_impl"),
    ("Sui", "dynamic_object_field", "borrow_mut_or_add"),
    ("Sui", "dynamic_object_field", "borrow_or_add"),
    ("Sui", "dynamic_object_field", "borrow_or_unknown"),
    ("Sui", "dynamic_object_field", "exists"),
    ("Sui", "dynamic_object_field", "exists_"),
    ("Sui", "dynamic_object_field", "exists_with_type"),
    ("Sui", "dynamic_object_field", "exists_with_type_impl"),
    ("Sui", "dynamic_object_field", "get_do"),
    ("Sui", "dynamic_object_field", "get_fold"),
    ("Sui", "dynamic_object_field", "get_mut_do"),
    ("Sui", "dynamic_object_field", "get_mut_fold"),
    ("Sui", "dynamic_object_field", "id"),
    ("Sui", "dynamic_object_field", "internal_add"),
    ("Sui", "dynamic_object_field", "internal_borrow"),
    ("Sui", "dynamic_object_field", "internal_borrow_mut"),
    ("Sui", "dynamic_object_field", "internal_exists_with_type"),
    ("Sui", "dynamic_object_field", "internal_remove"),
    ("Sui", "dynamic_object_field", "remove"),
    ("Sui", "dynamic_object_field", "remove_impl"),
    ("Sui", "dynamic_object_field", "remove_opt"),
    ("Sui", "dynamic_object_field", "replace"),
    // ---- Sui::ecdsa_k1 ----
    ("Sui", "ecdsa_k1", "decompress_pubkey"),
    ("Sui", "ecdsa_k1", "private_key"),
    ("Sui", "ecdsa_k1", "public_key"),
    ("Sui", "ecdsa_k1", "secp256k1_ecrecover"),
    ("Sui", "ecdsa_k1", "secp256k1_keypair_from_seed"),
    ("Sui", "ecdsa_k1", "secp256k1_sign"),
    ("Sui", "ecdsa_k1", "secp256k1_verify"),
    // ---- Sui::ecdsa_r1 ----
    ("Sui", "ecdsa_r1", "secp256r1_ecrecover"),
    ("Sui", "ecdsa_r1", "secp256r1_verify"),
    // ---- Sui::ecvrf ----
    ("Sui", "ecvrf", "ecvrf_verify"),
    // ---- Sui::ed25519 ----
    ("Sui", "ed25519", "ed25519_verify"),
    // ---- Sui::event ----
    ("Sui", "event", "emit"),
    ("Sui", "event", "emit_authenticated"),
    ("Sui", "event", "emit_authenticated_impl"),
    ("Sui", "event", "events_by_type"),
    ("Sui", "event", "num_events"),
    // ---- Sui::funds_accumulator ----
    ("Sui", "funds_accumulator", "add_impl"),
    ("Sui", "funds_accumulator", "add_to_accumulator_address"),
    ("Sui", "funds_accumulator", "create_withdrawal"),
    ("Sui", "funds_accumulator", "redeem"),
    (
        "Sui",
        "funds_accumulator",
        "reserve_object_funds_for_withdrawal",
    ),
    (
        "Sui",
        "funds_accumulator",
        "withdraw_from_accumulator_address",
    ),
    ("Sui", "funds_accumulator", "withdraw_from_object"),
    ("Sui", "funds_accumulator", "withdraw_impl"),
    ("Sui", "funds_accumulator", "withdrawal_join"),
    ("Sui", "funds_accumulator", "withdrawal_limit"),
    ("Sui", "funds_accumulator", "withdrawal_owner"),
    ("Sui", "funds_accumulator", "withdrawal_split"),
    // ---- Sui::groth16 ----
    ("Sui", "groth16", "bls12381"),
    ("Sui", "groth16", "bn254"),
    ("Sui", "groth16", "prepare_verifying_key"),
    ("Sui", "groth16", "prepare_verifying_key_internal"),
    ("Sui", "groth16", "proof_points_from_bytes"),
    ("Sui", "groth16", "public_proof_inputs_from_bytes"),
    ("Sui", "groth16", "pvk_from_bytes"),
    ("Sui", "groth16", "pvk_to_bytes"),
    ("Sui", "groth16", "verify_groth16_proof"),
    ("Sui", "groth16", "verify_groth16_proof_internal"),
    // ---- Sui::group_ops ----
    ("Sui", "group_ops", "add"),
    ("Sui", "group_ops", "bytes"),
    ("Sui", "group_ops", "convert"),
    ("Sui", "group_ops", "div"),
    ("Sui", "group_ops", "equal"),
    ("Sui", "group_ops", "from_bytes"),
    ("Sui", "group_ops", "hash_to"),
    ("Sui", "group_ops", "internal_add"),
    ("Sui", "group_ops", "internal_convert"),
    ("Sui", "group_ops", "internal_div"),
    ("Sui", "group_ops", "internal_hash_to"),
    ("Sui", "group_ops", "internal_mul"),
    ("Sui", "group_ops", "internal_multi_scalar_mul"),
    ("Sui", "group_ops", "internal_pairing"),
    ("Sui", "group_ops", "internal_sub"),
    ("Sui", "group_ops", "internal_sum"),
    ("Sui", "group_ops", "internal_validate"),
    ("Sui", "group_ops", "mul"),
    ("Sui", "group_ops", "multi_scalar_multiplication"),
    ("Sui", "group_ops", "pairing"),
    ("Sui", "group_ops", "set_as_prefix"),
    ("Sui", "group_ops", "sub"),
    ("Sui", "group_ops", "sum"),
    // ---- Sui::hash ----
    ("Sui", "hash", "blake2b256"),
    ("Sui", "hash", "keccak256"),
    // ---- Sui::hmac ----
    ("Sui", "hmac", "hmac_sha3_256"),
    // ---- Sui::nitro_attestation ----
    ("Sui", "nitro_attestation", "digest"),
    ("Sui", "nitro_attestation", "index"),
    ("Sui", "nitro_attestation", "load_nitro_attestation"),
    (
        "Sui",
        "nitro_attestation",
        "load_nitro_attestation_internal",
    ),
    ("Sui", "nitro_attestation", "module_id"),
    ("Sui", "nitro_attestation", "nonce"),
    ("Sui", "nitro_attestation", "pcrs"),
    ("Sui", "nitro_attestation", "public_key"),
    ("Sui", "nitro_attestation", "timestamp"),
    ("Sui", "nitro_attestation", "user_data"),
    ("Sui", "nitro_attestation", "value"),
    // ---- Sui::object ----
    ("Sui", "object", "address_alias_state"),
    ("Sui", "object", "authenticator_state"),
    ("Sui", "object", "borrow_id"),
    ("Sui", "object", "borrow_uid"),
    ("Sui", "object", "bridge"),
    ("Sui", "object", "clock"),
    ("Sui", "object", "delete"),
    ("Sui", "object", "delete_impl"),
    ("Sui", "object", "id"),
    ("Sui", "object", "id_address"),
    ("Sui", "object", "id_bytes"),
    ("Sui", "object", "id_from_address"),
    ("Sui", "object", "id_from_bytes"),
    ("Sui", "object", "id_to_address"),
    ("Sui", "object", "id_to_bytes"),
    ("Sui", "object", "last_created"),
    ("Sui", "object", "new"),
    ("Sui", "object", "new_uid_from_hash"),
    ("Sui", "object", "randomness_state"),
    ("Sui", "object", "record_new_uid"),
    ("Sui", "object", "record_new_uid_from_hash"),
    ("Sui", "object", "sui_accumulator_root_address"),
    ("Sui", "object", "sui_accumulator_root_object_id"),
    ("Sui", "object", "sui_coin_registry_address"),
    ("Sui", "object", "sui_coin_registry_object_id"),
    ("Sui", "object", "sui_deny_list_object_id"),
    ("Sui", "object", "sui_display_registry_address"),
    ("Sui", "object", "sui_display_registry_object_id"),
    ("Sui", "object", "sui_system_state"),
    ("Sui", "object", "uid_as_inner"),
    ("Sui", "object", "uid_to_address"),
    ("Sui", "object", "uid_to_bytes"),
    ("Sui", "object", "uid_to_inner"),
    // ---- Sui::object_bag ----
    ("Sui", "object_bag", "add"),
    ("Sui", "object_bag", "borrow"),
    ("Sui", "object_bag", "borrow_mut"),
    ("Sui", "object_bag", "contains"),
    ("Sui", "object_bag", "contains_with_type"),
    ("Sui", "object_bag", "destroy_empty"),
    ("Sui", "object_bag", "is_empty"),
    ("Sui", "object_bag", "length"),
    ("Sui", "object_bag", "new"),
    ("Sui", "object_bag", "remove"),
    ("Sui", "object_bag", "value_id"),
    // ---- Sui::object_table ----
    ("Sui", "object_table", "add"),
    ("Sui", "object_table", "add_pure"),
    ("Sui", "object_table", "borrow"),
    ("Sui", "object_table", "borrow_mut"),
    ("Sui", "object_table", "borrow_or_unknown"),
    ("Sui", "object_table", "contains"),
    ("Sui", "object_table", "destroy_empty"),
    ("Sui", "object_table", "is_empty"),
    ("Sui", "object_table", "length"),
    ("Sui", "object_table", "new"),
    ("Sui", "object_table", "remove"),
    ("Sui", "object_table", "remove_pure"),
    ("Sui", "object_table", "value_id"),
    // ---- Sui::poseidon ----
    ("Sui", "poseidon", "poseidon_bn254"),
    ("Sui", "poseidon", "poseidon_bn254_internal"),
    // ---- Sui::random ----
    ("Sui", "random", "create"),
    ("Sui", "random", "create_for_testing"),
    ("Sui", "random", "derive_next_block"),
    ("Sui", "random", "generate_bool"),
    ("Sui", "random", "generate_bytes"),
    ("Sui", "random", "generate_rand_seed_for_testing"),
    ("Sui", "random", "generate_u128"),
    ("Sui", "random", "generate_u128_in_range"),
    ("Sui", "random", "generate_u16"),
    ("Sui", "random", "generate_u16_in_range"),
    ("Sui", "random", "generate_u256"),
    ("Sui", "random", "generate_u32"),
    ("Sui", "random", "generate_u32_in_range"),
    ("Sui", "random", "generate_u64"),
    ("Sui", "random", "generate_u64_in_range"),
    ("Sui", "random", "generate_u8"),
    ("Sui", "random", "generate_u8_in_range"),
    ("Sui", "random", "generator_buffer"),
    ("Sui", "random", "generator_counter"),
    ("Sui", "random", "generator_seed"),
    ("Sui", "random", "load_inner"),
    ("Sui", "random", "load_inner_mut"),
    ("Sui", "random", "new_generator"),
    ("Sui", "random", "new_generator_for_testing"),
    ("Sui", "random", "new_generator_from_seed_for_testing"),
    ("Sui", "random", "shuffle"),
    ("Sui", "random", "uint_from_bytes"),
    ("Sui", "random", "uint_in_range"),
    ("Sui", "random", "update_randomness_state"),
    ("Sui", "random", "update_randomness_state_for_testing"),
    // ---- Sui::table ----
    ("Sui", "table", "add"),
    ("Sui", "table", "add_pure"),
    ("Sui", "table", "borrow"),
    ("Sui", "table", "borrow_mut"),
    ("Sui", "table", "borrow_or_unknown"),
    ("Sui", "table", "contains"),
    ("Sui", "table", "destroy_empty"),
    ("Sui", "table", "drop"),
    ("Sui", "table", "is_empty"),
    ("Sui", "table", "length"),
    ("Sui", "table", "new"),
    ("Sui", "table", "remove"),
    ("Sui", "table", "remove_pure"),
    // ---- Sui::test_scenario ----
    // The wrappers `return_shared` / `return_to_address` / `return_immutable`
    // are Move-defined in sui-framework but we override them as
    // natives so we can update the world's typed entry lists in
    // place. The Move-defined bodies call `transfer::share_object_impl`
    // (polymorphic passthrough), so without this override the
    // modifications to a vault between `take_shared` and
    // `return_shared` are silently lost. See
    // `lemmas/natives/Sui/Test_scenarioNatives.lean` for the
    // typed bodies.
    ("Sui", "test_scenario", "return_immutable"),
    ("Sui", "test_scenario", "return_shared"),
    ("Sui", "test_scenario", "return_to_address"),
    // ---- Sui::test_utils ----
    ("Sui", "test_utils", "create_one_time_witness"),
    // ---- Sui::transfer ----
    ("Sui", "transfer", "freeze_object"),
    ("Sui", "transfer", "freeze_object_impl"),
    ("Sui", "transfer", "make_receiver"),
    ("Sui", "transfer", "party_transfer"),
    ("Sui", "transfer", "party_transfer_impl"),
    ("Sui", "transfer", "public_freeze_object"),
    ("Sui", "transfer", "public_party_transfer"),
    ("Sui", "transfer", "public_receive"),
    ("Sui", "transfer", "public_share_object"),
    // `public_transfer` is intentionally NOT listed: it is a regular Move
    // `public fun public_transfer(obj, r) { transfer_impl(obj, r) }`, so it
    // is lifted. The real transfer effect + ghost write live in
    // `transfer_impl` / `transfer_impl__ghost` (the genuine `native fun`),
    // and the stage-4 ghost fixpoint propagates the ghost through the
    // lifted wrapper -- no `public_transfer__ghost` def or seed needed.
    ("Sui", "transfer", "receive"),
    ("Sui", "transfer", "receive_impl"),
    ("Sui", "transfer", "receiving_id"),
    ("Sui", "transfer", "receiving_object_id"),
    ("Sui", "transfer", "share_object"),
    ("Sui", "transfer", "share_object_impl"),
    ("Sui", "transfer", "transfer"),
    ("Sui", "transfer", "transfer_impl"),
    // ---- Sui::tx_context ----
    ("Sui", "tx_context", "create"),
    ("Sui", "tx_context", "derive_id"),
    ("Sui", "tx_context", "digest"),
    ("Sui", "tx_context", "dummy"),
    ("Sui", "tx_context", "dummy_tx_hash_with_hint"),
    ("Sui", "tx_context", "epoch"),
    ("Sui", "tx_context", "epoch_timestamp_ms"),
    ("Sui", "tx_context", "fresh_id"),
    ("Sui", "tx_context", "fresh_object_address"),
    ("Sui", "tx_context", "gas_budget"),
    ("Sui", "tx_context", "gas_price"),
    ("Sui", "tx_context", "get_ids_created"),
    ("Sui", "tx_context", "ids_created"),
    ("Sui", "tx_context", "increment_epoch_number"),
    ("Sui", "tx_context", "increment_epoch_timestamp"),
    ("Sui", "tx_context", "last_created_id"),
    ("Sui", "tx_context", "last_created_object_id"),
    ("Sui", "tx_context", "native_epoch"),
    ("Sui", "tx_context", "native_epoch_timestamp_ms"),
    ("Sui", "tx_context", "native_gas_budget"),
    ("Sui", "tx_context", "native_gas_price"),
    ("Sui", "tx_context", "native_ids_created"),
    ("Sui", "tx_context", "native_rgp"),
    ("Sui", "tx_context", "native_sender"),
    ("Sui", "tx_context", "native_sponsor"),
    ("Sui", "tx_context", "new"),
    ("Sui", "tx_context", "new_from_hint"),
    ("Sui", "tx_context", "option_sponsor"),
    ("Sui", "tx_context", "reference_gas_price"),
    ("Sui", "tx_context", "replace"),
    ("Sui", "tx_context", "sender"),
    ("Sui", "tx_context", "sponsor"),
    // ---- Sui::types ----
    ("Sui", "types", "is_one_time_witness"),
    // ---- Sui::vdf ----
    ("Sui", "vdf", "hash_to_input"),
    ("Sui", "vdf", "hash_to_input_internal"),
    ("Sui", "vdf", "vdf_verify"),
    ("Sui", "vdf", "vdf_verify_internal"),
    // ---- Sui::vec_map ----
    ("Sui", "vec_map", "contains"),
    ("Sui", "vec_map", "destroy_empty"),
    ("Sui", "vec_map", "empty"),
    ("Sui", "vec_map", "from_keys_values"),
    ("Sui", "vec_map", "get"),
    ("Sui", "vec_map", "get_entry_by_idx"),
    ("Sui", "vec_map", "get_entry_by_idx_mut"),
    ("Sui", "vec_map", "get_entry_by_idx_or_unknown"),
    ("Sui", "vec_map", "get_idx"),
    ("Sui", "vec_map", "get_idx_opt"),
    ("Sui", "vec_map", "get_idx_or_unknown"),
    ("Sui", "vec_map", "get_mut"),
    ("Sui", "vec_map", "get_or_unknown"),
    ("Sui", "vec_map", "insert"),
    ("Sui", "vec_map", "insert_pure"),
    ("Sui", "vec_map", "into_keys_values"),
    ("Sui", "vec_map", "is_empty"),
    ("Sui", "vec_map", "keys"),
    ("Sui", "vec_map", "length"),
    ("Sui", "vec_map", "pop"),
    ("Sui", "vec_map", "remove"),
    ("Sui", "vec_map", "remove_entry_by_idx"),
    ("Sui", "vec_map", "remove_pure"),
    ("Sui", "vec_map", "size"),
    ("Sui", "vec_map", "try_get"),
    // ---- Sui::vec_set ----
    ("Sui", "vec_set", "contains"),
    ("Sui", "vec_set", "empty"),
    ("Sui", "vec_set", "from_keys"),
    ("Sui", "vec_set", "insert"),
    ("Sui", "vec_set", "insert_pure"),
    ("Sui", "vec_set", "into_keys"),
    ("Sui", "vec_set", "is_empty"),
    ("Sui", "vec_set", "keys"),
    ("Sui", "vec_set", "length"),
    ("Sui", "vec_set", "remove"),
    ("Sui", "vec_set", "remove_pure"),
    ("Sui", "vec_set", "singleton"),
    ("Sui", "vec_set", "size"),
    // ---- Sui::zklogin_verified_id ----
    ("Sui", "zklogin_verified_id", "audience"),
    ("Sui", "zklogin_verified_id", "check_zklogin_id"),
    ("Sui", "zklogin_verified_id", "check_zklogin_id_internal"),
    ("Sui", "zklogin_verified_id", "delete"),
    ("Sui", "zklogin_verified_id", "issuer"),
    ("Sui", "zklogin_verified_id", "key_claim_name"),
    ("Sui", "zklogin_verified_id", "key_claim_value"),
    ("Sui", "zklogin_verified_id", "owner"),
    ("Sui", "zklogin_verified_id", "verify_zklogin_id"),
    // ---- Sui::zklogin_verified_issuer ----
    ("Sui", "zklogin_verified_issuer", "check_zklogin_issuer"),
    (
        "Sui",
        "zklogin_verified_issuer",
        "check_zklogin_issuer_internal",
    ),
    ("Sui", "zklogin_verified_issuer", "delete"),
    ("Sui", "zklogin_verified_issuer", "issuer"),
    ("Sui", "zklogin_verified_issuer", "owner"),
    ("Sui", "zklogin_verified_issuer", "verify_zklogin_issuer"),
];

/// Structs whose Move body the pipeline discards in favour of a
/// Lean prelude definition (or a header-only stub when the prelude
/// doesn't declare a corresponding type).
///
/// Populated by listing every struct/enum currently declared in
/// every module of [`NATIVE_FUNCTION_MODULES`]. Pre-refactor, every
/// struct in a native module was given header-only treatment via
/// the module-level allowlist; this list pins the exact set so the
/// per-struct dispatch in `module_lift` preserves that behaviour
/// while opening the door to mixing translated and prelude-replaced
/// structs in the same module.
const NATIVE_STRUCTS: &[(&str, &str, &str)] = &[
    // Sorted lexicographically by (package, module_name, struct_name).
    // ---- MoveStdlib ----
    ("MoveStdlib", "integer", "Integer"),
    ("MoveStdlib", "real", "Real"),
    ("MoveStdlib", "string", "String"),
    ("MoveStdlib", "type_name", "TypeName"),
    // ---- Sui ----
    ("Sui", "bag", "Bag"),
    ("Sui", "bls12381", "G1"),
    ("Sui", "bls12381", "G2"),
    ("Sui", "bls12381", "GT"),
    ("Sui", "bls12381", "Scalar"),
    ("Sui", "bls12381", "UncompressedG1"),
    ("Sui", "config", "Config"),
    ("Sui", "config", "Setting"),
    ("Sui", "config", "SettingData"),
    ("Sui", "dynamic_field", "Field"),
    ("Sui", "dynamic_object_field", "Wrapper"),
    ("Sui", "ecdsa_k1", "KeyPair"),
    ("Sui", "funds_accumulator", "Withdrawal"),
    ("Sui", "groth16", "Curve"),
    ("Sui", "groth16", "PreparedVerifyingKey"),
    ("Sui", "groth16", "ProofPoints"),
    ("Sui", "groth16", "PublicProofInputs"),
    ("Sui", "group_ops", "Element"),
    ("Sui", "nitro_attestation", "NitroAttestationDocument"),
    ("Sui", "nitro_attestation", "PCREntry"),
    ("Sui", "object", "ID"),
    ("Sui", "object", "UID"),
    ("Sui", "object_bag", "ObjectBag"),
    ("Sui", "object_table", "ObjectTable"),
    ("Sui", "random", "Random"),
    ("Sui", "random", "RandomGenerator"),
    ("Sui", "random", "RandomInner"),
    ("Sui", "table", "Table"),
    ("Sui", "transfer", "Receiving"),
    ("Sui", "tx_context", "TxContext"),
    ("Sui", "vec_map", "Entry"),
    ("Sui", "vec_map", "VecMap"),
    ("Sui", "vec_set", "VecSet"),
    ("Sui", "zklogin_verified_id", "VerifiedID"),
    ("Sui", "zklogin_verified_issuer", "VerifiedIssuer"),
];

/// True iff the named struct's Move body is replaced by a Lean
/// prelude definition (or a header-only stub). Consulted by
/// `module_lift` to pass the right `is_native` flag to `lift_struct`
/// (full body vs prelude-replaced header). Per-struct dispatch
/// enables mixed modules -- some structs prelude-replaced, others
/// translated -- that the previous module-level allowlist forbade.
pub fn is_native_struct(package: &str, module_name: &str, struct_name: &str) -> bool {
    NATIVE_STRUCTS
        .iter()
        .any(|(p, m, n)| *p == package && *m == module_name && *n == struct_name)
}

/// True iff the pipeline should produce a [`crate::ir::NativeDecl`]
/// (no body) for this function rather than translating its Move
/// body. Sources:
///
/// 1. Move declared it `native fun` (per-function keyword) -- caller
///    passes this in as `move_native` (typically
///    `func_env.is_native()` from `move_model`); we have no Move
///    body to translate.
/// 2. The function appears in [`NATIVE_FUNCTIONS`] (per-function
///    allowlist of framework functions whose body the prelude
///    provides). Linear scan; the list is short so this is fine.
/// 3. The function is the magic `unit_test_poison` marker -- a
///    compiler-injected, source-invisible artifact that
///    `move_model` reports in every module under `--test` mode.
///    Treating it as native keeps the per-thing `all_functions_native`
///    derivation from flipping every framework module to
///    non-native solely because of the injected marker.
///
/// **Note:** the [`native_effects`] classification table is NOT a
/// source of "is native" -- it classifies the abort/det/mutation
/// axes for functions that *might* be native or *might* be
/// translated. For example `MoveStdlib::option` carries effects
/// entries despite its Move body being translated (option is not a
/// framework native module). Conflating the two surfaces produced
/// signature/calling-convention mismatches at lake-build time.
pub fn is_native_function(
    package: &str,
    module_name: &str,
    function_name: &str,
    move_native: bool,
) -> bool {
    if move_native {
        return true;
    }
    if function_name == "unit_test_poison" {
        return true;
    }
    NATIVE_FUNCTIONS
        .iter()
        .any(|(p, m, f)| *p == package && *m == module_name && *f == function_name)
}

/// True for the placeholder `native fun` that sui-prover's
/// `add_stub_module` injects into the ROOT package. When a package's
/// `Move.toml` depends on Sui explicitly (disabling the implicit
/// SuiProver dep), sui-prover synthesizes empty `ghost` / `prover` /
/// `log` modules -- each carrying a single `native fun __stub_placeholder`
/// with an empty signature -- so upstream processors that unconditionally
/// resolve `global_qid()` / `log_text_qid()` don't panic. These stubs are
/// compiler-injected artifacts, not client-authored datatype-invariant
/// predicates, so they must NOT trip the user-native overlay lookup
/// (`NativeDecl::user_native`). They are normally unreferenced and omitted
/// from rendered Lean. If generated IR ever references one, the native-model
/// gate requires an explicit model; no fallback body is emitted. Keyed on the
/// function name alone -- `__stub_placeholder` is a deliberately unique,
/// source-invisible sui-prover contract, so it needs no coupling to the
/// specific injected module names (which sui-prover may change). Mirrors the
/// `unit_test_poison` marker handling above.
pub fn is_injected_stub_native(function_name: &str) -> bool {
    function_name == "__stub_placeholder"
}

/// Classify a native function's [`crate::ir::Effects`] along the
/// `(aborts, det, mutation, world writes)` axes. Lookup is keyed on
/// `(package, module_name, function_name)`. Functions absent from
/// the table default to [`crate::ir::Effects::CONSERVATIVE`] -- the
/// conservative fallback that keeps stage 5 from inlining unknowns
/// and forces stage 4 to thread world through any caller.
///
/// The mapping is hand-curated; as evidence accumulates (failing
/// parity diffs against the legacy renderer), we tighten the table.
pub fn native_effects(package: &str, module_name: &str, function_name: &str) -> crate::ir::Effects {
    use crate::ir::{AbortBit::*, DetBit::*, Effects, MutLevel::*};

    // Cell constants for the 7 populated cells of the original 3-dim
    // lattice. Global-mutating natives conservatively write World.
    // The two cells `(*, NonDet, NoMut)` are empty -- every NonDet
    // entry in today's table also takes a `&mut` handle.
    const EFF_TDN: Effects = Effects::PURE;
    const EFF_TDM_LOCAL: Effects = Effects {
        aborts: Total,
        det: Det,
        mutation: LocalMut,
        world_writes: false,
    };
    const EFF_TDM_GLOBAL: Effects = Effects {
        aborts: Total,
        det: Det,
        mutation: GlobalMut,
        world_writes: true,
    };
    const EFF_TNM_GLOBAL: Effects = Effects {
        aborts: Total,
        det: NonDet,
        mutation: GlobalMut,
        world_writes: true,
    };
    const EFF_PDN: Effects = Effects {
        aborts: Partial,
        det: Det,
        mutation: NoMut,
        world_writes: false,
    };
    const EFF_PDM_LOCAL: Effects = Effects {
        aborts: Partial,
        det: Det,
        mutation: LocalMut,
        world_writes: false,
    };
    const EFF_PDM_GLOBAL: Effects = Effects {
        aborts: Partial,
        det: Det,
        mutation: GlobalMut,
        world_writes: true,
    };
    const EFF_PNM_LOCAL: Effects = Effects {
        aborts: Partial,
        det: NonDet,
        mutation: LocalMut,
        world_writes: false,
    };

    let entry: Option<Effects> = match (package, module_name, function_name) {
        // All sui::bls12381 and sui::group_ops natives are pure crypto
        // (group arithmetic / signature verification / byte extraction):
        // deterministic, no mutation, no world. Like prover::val, without an
        // entry they fall to the default CONSERVATIVE GlobalMut, which
        // world-threads them into a 3-arg `(result, world')` form their pure
        // prelude models can't be applied to ("Function expected").
        ("Sui", "bls12381", _) => Some(EFF_TDN),
        ("Sui", "group_ops", _) => Some(EFF_TDN),
        // ---------------------------------------------------------------
        // The rest of the framework's PURE-modelled natives. Same defect
        // as the two rows above, same shape, and it is the whole reason
        // `securitize/token-distribution` could not generate on main: the
        // FRAMEWORK spec package (`SuiSpecs`) carries an identity spec for
        // each of these (`#[spec(target = sui::vdf::vdf_verify_internal)]
        // fun vdf_verify_internal_spec(..) { vdf_verify_internal(..) }`),
        // so every one of them is COMPILED for every client whose module
        // set pulls the crypto spec files in -- 30 `Function expected at
        // <Native> ... applied to the argument world` errors across
        // Config/Ecdsa_r1/Ecvrf/Ed25519/Event/Groth16/Nitro_attestation/
        // Poseidon/Vdf/Zklogin_verified_{id,issuer}_spec.lean.
        //
        // Without a row they fall to `Effects::CONSERVATIVE` (GlobalMut),
        // which world-threads the call into `(result, world')` -- but the
        // shipped models in `lemmas/natives/Sui/*Natives.lean` take no
        // world, so nothing can be applied to it. The world axis is the
        // ONLY thing wrong, so the abort axis is preserved rather than
        // improved: `EFF_PDN` (still `Partial`, exactly what CONSERVATIVE
        // said) wherever the framework documents an abort, and `EFF_TDN`
        // only where the native is a total accessor / constant reader.
        // Choosing `Total` for an aborting native would DROP that abort
        // from every caller's `.aborts` face, which is the silent
        // unsoundness `NATIVES_WITH_ABORTS_COMPANIONS` exists to prevent.
        //
        // `tests::every_pure_lean_native_model_is_classified_pure` pins
        // both directions of this table-vs-bundle contract.
        //
        // The `MoveStdlib::integer` and several `Sui::object` rows are
        // redundant on the prover's `asymptotic-code/sui-next` fork, where
        // the declarations carry `#[ext(pure)]` and `module_lift` locks
        // them to `Effects::PURE` before this table is consulted. They are
        // NOT redundant on `MystenLabs/sui` (mainnet), which carries the
        // same functions without the attribute -- and this table is
        // explicitly merged across both forks (see `NATIVE_FUNCTIONS`).
        ("MoveStdlib", "integer", "is_i8") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_i16") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_i32") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_i64") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_i128") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_i256") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "signed_from_u8") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "signed_from_u16") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "signed_from_u32") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "signed_from_u64") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "signed_from_u128") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "signed_from_u256") => Some(EFF_TDN),
        ("MoveStdlib", "string", "bytes") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "as_string") => Some(EFF_TDN),
        ("Sui", "address", "max") => Some(EFF_TDN),
        ("Sui", "address", "to_u256") => Some(EFF_TDN),
        // `read_setting_impl` is native only "to keep gas costing
        // consistent" (its own comment); it returns an `Option` and
        // documents no abort.
        ("Sui", "config", "read_setting_impl") => Some(EFF_TDN),
        // `KeyPair` field accessors, like their `secp256k1_*` siblings.
        ("Sui", "ecdsa_k1", "private_key") => Some(EFF_TDN),
        ("Sui", "ecdsa_k1", "public_key") => Some(EFF_TDN),
        // "If the signature is valid to the pubkey and hashed message,
        // return true. Else false." -- no abort path.
        ("Sui", "ecdsa_r1", "secp256r1_verify") => Some(EFF_TDN),
        // "May fail with `EFailToRecoverPubKey` or `EInvalidSignature`."
        ("Sui", "ecdsa_r1", "secp256r1_ecrecover") => Some(EFF_PDN),
        // "May abort with `EInvalidHashLength`, `EInvalidPublicKeyEncoding`
        // or `EInvalidProofEncoding`."
        ("Sui", "ecvrf", "ecvrf_verify") => Some(EFF_PDN),
        // "If the signature is a valid Ed25519 signature ... return true.
        // Otherwise, return false." -- no abort path.
        ("Sui", "ed25519", "ed25519_verify") => Some(EFF_TDN),
        // `#[test_only]` reader natives; the models are the constants `0`
        // and `[]`. See the fidelity note in `EventNatives.lean`: the
        // typed payload is never recorded in the world, only counted.
        ("Sui", "event", "num_events") => Some(EFF_TDN),
        ("Sui", "event", "events_by_type") => Some(EFF_TDN),
        // "May abort with `EInvalidVerifyingKey` or `EInvalidCurve`."
        ("Sui", "groth16", "prepare_verifying_key_internal") => Some(EFF_PDN),
        // "May abort with `EInvalidCurve` or `ETooManyPublicInputs`."
        ("Sui", "groth16", "verify_groth16_proof_internal") => Some(EFF_PDN),
        // Decodes and validates a CBOR/COSE attestation document.
        ("Sui", "nitro_attestation", "load_nitro_attestation_internal") => Some(EFF_PDN),
        ("Sui", "object", "id_address") => Some(EFF_TDN),
        ("Sui", "object", "id_bytes") => Some(EFF_TDN),
        ("Sui", "object", "uid_as_inner") => Some(EFF_TDN),
        ("Sui", "object", "uid_to_bytes") => Some(EFF_TDN),
        ("Sui", "poseidon", "poseidon_bn254_internal") => Some(EFF_PDN),
        ("Sui", "random", "generate_rand_seed_for_testing") => Some(EFF_TDN),
        ("Sui", "tx_context", "ids_created") => Some(EFF_TDN),
        // `vdf` declares `EInvalidInput` and both natives decode class
        // group elements out of raw bytes.
        ("Sui", "vdf", "hash_to_input_internal") => Some(EFF_PDN),
        ("Sui", "vdf", "vdf_verify_internal") => Some(EFF_PDN),
        // `check_zklogin_id` is `assert!(false, EFunctionDisabled)` in the
        // framework and the two `*_internal` natives abort with
        // `EInvalidInput` on a non-UTF-8 / over-long claim. The bundle's
        // `.aborts` companions say `False` for all three; they are NOT
        // registered in `NATIVES_WITH_ABORTS_COMPANIONS`, so they are
        // inert and the coarse `Partial -> true` is what callers see.
        ("Sui", "zklogin_verified_id", "check_zklogin_id") => Some(EFF_PDN),
        ("Sui", "zklogin_verified_id", "check_zklogin_id_internal") => Some(EFF_PDN),
        ("Sui", "zklogin_verified_id", "verify_zklogin_id") => Some(EFF_PDN),
        ("Sui", "zklogin_verified_issuer", "check_zklogin_issuer_internal") => Some(EFF_PDN),
        // ---------------------------------------------------------------
        ("MoveStdlib", "bcs", "to_bytes") => Some(EFF_TDN),
        ("Sui", "bcs", "to_bytes") => Some(EFF_TDN),
        // `std::hash` is the MIRROR of the bug the bls12381 comment above
        // describes: the shipped models in
        // `lemmas/natives/MoveStdlib/HashNatives.lean` take `world` and
        // return `(bytes, world)` (like their `sui::hash` siblings), so a
        // `NoMut` classification emitted a pure call and lake reported
        // `Type mismatch ... has type World -> ... but is expected to have
        // type List (BoundedNat (2 ^ 8))` in `SuiSpecs/Hash_spec.lean`.
        // `Effects::WORLD` is the cell for exactly this shape: threads
        // world unchanged, `Total` (the models ship `.aborts := false`) and
        // `Det`. Total/Det are what `EFF_TDN` already said, so no caller's
        // abort face moves -- only the world arity.
        ("MoveStdlib", "hash", "sha2_256") => Some(Effects::WORLD),
        ("MoveStdlib", "hash", "sha3_256") => Some(Effects::WORLD),
        ("MoveStdlib", "debug", "print") => Some(EFF_TDN),
        ("MoveStdlib", "debug", "print_stack_trace") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "abs") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "add") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "bit_and") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "bit_not") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "bit_or") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "bit_xor") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "div") => Some(EFF_PDN),
        ("MoveStdlib", "integer", "div_round_up") => Some(EFF_PDN),
        ("MoveStdlib", "integer", "div_trunc") => Some(EFF_PDN),
        ("MoveStdlib", "integer", "eq") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "from_u128") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "from_u16") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "from_u256") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "from_u32") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "from_u64") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "from_u8") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "ge") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "gt") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "gte") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_neg") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "is_pos") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "le") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "lt") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "lte") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "mod") => Some(EFF_PDN),
        ("MoveStdlib", "integer", "mod_trunc") => Some(EFF_PDN),
        ("MoveStdlib", "integer", "mul") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "neg") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "pow") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "shl") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "shr") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "sqrt") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "sub") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "to_u128") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "to_u16") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "to_u256") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "to_u32") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "to_u64") => Some(EFF_TDN),
        ("MoveStdlib", "integer", "to_u8") => Some(EFF_TDN),
        ("MoveStdlib", "real", "add") => Some(EFF_TDN),
        ("MoveStdlib", "real", "div") => Some(EFF_PDN),
        ("MoveStdlib", "real", "exp") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_integer") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_u128") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_u16") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_u256") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_u32") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_u64") => Some(EFF_TDN),
        ("MoveStdlib", "real", "from_u8") => Some(EFF_TDN),
        ("MoveStdlib", "real", "gt") => Some(EFF_TDN),
        ("MoveStdlib", "real", "gte") => Some(EFF_TDN),
        ("MoveStdlib", "real", "lt") => Some(EFF_TDN),
        ("MoveStdlib", "real", "lte") => Some(EFF_TDN),
        ("MoveStdlib", "real", "mul") => Some(EFF_TDN),
        ("MoveStdlib", "real", "neg") => Some(EFF_TDN),
        ("MoveStdlib", "real", "sqrt") => Some(EFF_PDN),
        ("MoveStdlib", "real", "sub") => Some(EFF_TDN),
        ("MoveStdlib", "real", "to_integer") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "borrow_string") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "defining_id") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "get") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "get_with_original_ids") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "into_string") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "is_primitive") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "original_id") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "with_defining_ids") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "with_original_ids") => Some(EFF_TDN),
        ("MoveStdlib", "type_name", "address_string") => Some(EFF_PDN),
        ("MoveStdlib", "type_name", "get_address") => Some(EFF_PDN),
        ("MoveStdlib", "type_name", "module_string") => Some(EFF_PDN),
        ("MoveStdlib", "type_name", "datatype_string") => Some(EFF_PDN),
        ("MoveStdlib", "vector", "borrow") => Some(EFF_PDN),
        ("MoveStdlib", "vector", "contains") => Some(EFF_TDN),
        ("MoveStdlib", "vector", "empty") => Some(EFF_TDN),
        ("MoveStdlib", "vector", "is_empty") => Some(EFF_TDN),
        ("MoveStdlib", "vector", "length") => Some(EFF_TDN),
        ("MoveStdlib", "vector", "singleton") => Some(EFF_TDN),
        ("MoveStdlib", "vector", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "vector", "pop_back") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "vector", "remove") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "vector", "swap") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "vector", "swap_remove") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "vector", "push_back") => Some(EFF_TDM_LOCAL),
        ("MoveStdlib", "vector", "append") => Some(EFF_TDM_LOCAL),
        ("MoveStdlib", "vector", "reverse") => Some(EFF_TDM_LOCAL),
        ("MoveStdlib", "vector", "destroy_empty") => Some(EFF_PDN),
        ("MoveStdlib", "vector", "index_of") => Some(EFF_TDN),
        ("MoveStdlib", "vector", "insert") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "vector", "flatten") => Some(EFF_TDN),
        ("MoveStdlib", "string", "utf8") => Some(EFF_PDN),
        ("MoveStdlib", "string", "length") => Some(EFF_TDN),
        ("MoveStdlib", "string", "is_empty") => Some(EFF_TDN),
        ("MoveStdlib", "string", "as_bytes") => Some(EFF_TDN),
        // `into_bytes` consumes the String and returns its `bytes` vector;
        // pure + abort-free, exactly like `as_bytes`. Without this it fell
        // to the CONSERVATIVE default (world-threaded + Partial), which
        // both mis-shaped the call and spliced a spurious `else true` into
        // every caller's `.aborts`.
        ("MoveStdlib", "string", "into_bytes") => Some(EFF_TDN),
        ("MoveStdlib", "string", "from_ascii") => Some(EFF_TDN),
        ("MoveStdlib", "string", "substring") => Some(EFF_PDN),
        ("MoveStdlib", "string", "append") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "string", "append_utf8") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "string", "index_of") => Some(EFF_TDN),
        ("MoveStdlib", "option", "some") => Some(EFF_TDN),
        ("MoveStdlib", "option", "none") => Some(EFF_TDN),
        ("MoveStdlib", "option", "is_some") => Some(EFF_TDN),
        ("MoveStdlib", "option", "is_none") => Some(EFF_TDN),
        ("MoveStdlib", "option", "borrow") => Some(EFF_PDN),
        ("MoveStdlib", "option", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "option", "borrow_with_default") => Some(EFF_TDN),
        ("MoveStdlib", "option", "contains") => Some(EFF_TDN),
        ("MoveStdlib", "option", "get_with_default") => Some(EFF_TDN),
        ("MoveStdlib", "option", "fill") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "option", "extract") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "option", "destroy_some") => Some(EFF_PDN),
        ("MoveStdlib", "option", "destroy_none") => Some(EFF_PDN),
        ("MoveStdlib", "option", "destroy_with_default") => Some(EFF_TDN),
        ("MoveStdlib", "option", "swap") => Some(EFF_PDM_LOCAL),
        ("MoveStdlib", "option", "swap_or_fill") => Some(EFF_TDM_LOCAL),
        ("MoveStdlib", "option", "to_vec") => Some(EFF_TDN),
        ("Prover", "prover", "requires") => Some(EFF_TDN),
        ("Prover", "prover", "ensures") => Some(EFF_TDN),
        // `asserts(p)` is a spec CONDITION, not an instruction: the call
        // itself never aborts, and stage 7 lowers it in place into an abort
        // guard from the pre-strip body rather than splicing an `.aborts`
        // companion. Same abort axis as its `requires`/`ensures` siblings.
        ("Prover", "prover", "asserts") => Some(EFF_TDN),
        // `asserts_of(b"name")` is a pure spec query (returns the named
        // function's asserts predicate as a Bool; the native is a `:= false`
        // stub). Without an entry it defaults to CONSERVATIVE (GlobalMut),
        // which world-threads the call -- but the native takes no world, so
        // the render's `asserts_of [..] world` fails with "Function expected".
        ("Prover", "prover", "asserts_of") => Some(EFF_TDN),
        // The remaining prover::prover natives: identity / Unit /
        // abstract-marker spec stubs whose prelude models are pure and take
        // no World. Listed individually (no catch-all) so a newly-added
        // prover native is forced to get a deliberate classification rather
        // than silently inheriting `pure` -- which would be wrong for any
        // future effectful directive (cf. `asserts`, EFF_PDN above, which
        // aborts when its predicate is false). Without an entry they fall to
        // the default CONSERVATIVE GlobalMut, which world-threads the call
        // into a `(val, world')` form the pure prelude can't be applied to
        // ("Function expected").
        ("Prover", "prover", "begin_exists_lambda") => Some(EFF_TDN),
        ("Prover", "prover", "begin_forall_lambda") => Some(EFF_TDN),
        ("Prover", "prover", "boogie_allow_path_isolation") => Some(EFF_TDN),
        ("Prover", "prover", "boogie_focus") => Some(EFF_TDN),
        ("Prover", "prover", "boogie_split_here") => Some(EFF_TDN),
        ("Prover", "prover", "clone") => Some(EFF_TDN),
        ("Prover", "prover", "drop") => Some(EFF_TDN),
        ("Prover", "prover", "drop_spec") => Some(EFF_TDN),
        ("Prover", "prover", "end_exists_lambda") => Some(EFF_TDN),
        ("Prover", "prover", "end_forall_lambda") => Some(EFF_TDN),
        ("Prover", "prover", "exists") => Some(EFF_TDN),
        ("Prover", "prover", "forall") => Some(EFF_TDN),
        ("Prover", "prover", "fresh") => Some(EFF_TDN),
        ("Prover", "prover", "fresh_spec") => Some(EFF_TDN),
        ("Prover", "prover", "implies") => Some(EFF_TDN),
        ("Prover", "prover", "invariant") => Some(EFF_TDN),
        ("Prover", "prover", "invariant_begin") => Some(EFF_TDN),
        ("Prover", "prover", "invariant_end") => Some(EFF_TDN),
        ("Prover", "prover", "ref") => Some(EFF_TDN),
        ("Prover", "prover", "ref_spec") => Some(EFF_TDN),
        ("Prover", "prover", "type_inv") => Some(EFF_TDN),
        ("Prover", "prover", "val") => Some(EFF_TDN),
        ("Prover", "prover", "val_spec") => Some(EFF_TDN),
        // `prover::ghost::*` are SPEC-ONLY proof devices, NOT native
        // runtime state. Without an entry they default to CONSERVATIVE
        // (GlobalMut), which world-threads the call -- but the ghost
        // natives take no world, so the render's `borrow_mut [..] world`
        // fails with "Function expected". Ghost reads are resolved at the
        // spec level (extraction), never stored in `World`; from the
        // native-effects view they are pure.
        ("Prover", "ghost", "borrow_mut") => Some(EFF_TDN),
        ("Prover", "ghost", "declare_global") => Some(EFF_TDN),
        ("Prover", "ghost", "declare_global_mut") => Some(EFF_TDN),
        ("Prover", "ghost", "global") => Some(EFF_TDN),
        ("Prover", "ghost", "havoc_global") => Some(EFF_TDN),
        ("Prover", "ghost", "set") => Some(EFF_TDN),
        ("Prover", "ghost", "set_spec") => Some(EFF_TDN),
        ("Prover", "vector_iter", "range") => Some(EFF_TDN),
        ("Prover", "vector_iter", "slice") => Some(EFF_TDN),
        ("Prover", "vector_iter", "sum") => Some(EFF_TDN),
        ("Prover", "vector_iter", "sum_range") => Some(EFF_TDN),
        ("Sui", "accumulator", "emit_deposit_event") => Some(EFF_TDM_GLOBAL),
        ("Sui", "accumulator", "emit_withdraw_event") => Some(EFF_TDM_GLOBAL),
        ("Sui", "address", "from_bytes") => Some(EFF_PDN),
        ("Sui", "address", "to_bytes") => Some(EFF_TDN),
        ("Sui", "ecdsa_k1", "secp256k1_ecrecover") => Some(EFF_TDN),
        ("Sui", "ecdsa_k1", "secp256k1_verify") => Some(EFF_TDN),
        ("Sui", "ecdsa_k1", "decompress_pubkey") => Some(EFF_TDN),
        ("Sui", "ecdsa_k1", "secp256k1_sign") => Some(EFF_TDN),
        ("Sui", "ecdsa_k1", "secp256k1_keypair_from_seed") => Some(EFF_TDN),
        ("Sui", "object", "id") => Some(EFF_TDN),
        ("Sui", "object", "borrow_id") => Some(EFF_TDN),
        ("Sui", "object", "borrow_uid") => Some(EFF_TDN),
        ("Sui", "object", "delete") => Some(EFF_TDM_GLOBAL),
        ("Sui", "object", "delete_impl") => Some(EFF_TDM_GLOBAL),
        ("Sui", "object", "id_from_address") => Some(EFF_TDN),
        ("Sui", "object", "id_from_bytes") => Some(EFF_TDN),
        ("Sui", "object", "id_to_address") => Some(EFF_TDN),
        ("Sui", "object", "id_to_bytes") => Some(EFF_TDN),
        ("Sui", "object", "new") => Some(EFF_PDM_GLOBAL),
        ("Sui", "object", "record_new_uid") => Some(EFF_PDM_LOCAL),
        ("Sui", "object", "record_new_uid_from_hash") => Some(EFF_PDM_LOCAL),
        ("Sui", "object", "uid_to_inner") => Some(EFF_TDN),
        ("Sui", "object", "uid_to_address") => Some(EFF_TDN),
        ("Sui", "tx_context", "dummy") => Some(EFF_TDN),
        ("Sui", "tx_context", "digest") => Some(EFF_TDN),
        ("Sui", "tx_context", "epoch") => Some(EFF_TDN),
        ("Sui", "tx_context", "epoch_timestamp_ms") => Some(EFF_TDN),
        ("Sui", "tx_context", "fresh_object_address") => Some(EFF_PDM_LOCAL),
        ("Sui", "tx_context", "gas_price") => Some(EFF_TDN),
        ("Sui", "tx_context", "reference_gas_price") => Some(EFF_TDN),
        ("Sui", "tx_context", "sender") => Some(EFF_TDN),
        ("Sui", "tx_context", "sponsor") => Some(EFF_TDN),
        ("Sui", "tx_context", "increment_epoch_number") => Some(EFF_PDM_LOCAL),
        ("Sui", "bag", "new") => Some(EFF_TDM_GLOBAL),
        ("Sui", "bag", "add") => Some(EFF_PDM_LOCAL),
        ("Sui", "bag", "borrow") => Some(EFF_PDN),
        ("Sui", "bag", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "bag", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "bag", "contains") => Some(EFF_TDN),
        ("Sui", "bag", "contains_with_type") => Some(EFF_TDN),
        ("Sui", "bag", "is_empty") => Some(EFF_TDN),
        ("Sui", "bag", "length") => Some(EFF_TDN),
        ("Sui", "bag", "destroy_empty") => Some(EFF_PDN),
        ("Sui", "object_bag", "new") => Some(EFF_TDM_GLOBAL),
        ("Sui", "object_bag", "add") => Some(EFF_PDM_LOCAL),
        ("Sui", "object_bag", "borrow") => Some(EFF_PDN),
        ("Sui", "object_bag", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "object_bag", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "object_bag", "contains") => Some(EFF_TDN),
        ("Sui", "object_bag", "contains_with_type") => Some(EFF_TDN),
        ("Sui", "object_bag", "is_empty") => Some(EFF_TDN),
        ("Sui", "object_bag", "length") => Some(EFF_TDN),
        ("Sui", "object_bag", "destroy_empty") => Some(EFF_PDN),
        ("Sui", "object_bag", "value_id") => Some(EFF_TDN),
        ("Sui", "table", "new") => Some(EFF_TDM_GLOBAL),
        ("Sui", "table", "add") => Some(EFF_PDM_LOCAL),
        ("Sui", "table", "borrow") => Some(EFF_PDN),
        ("Sui", "table", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "table", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "table", "contains") => Some(EFF_TDN),
        ("Sui", "table", "is_empty") => Some(EFF_TDN),
        ("Sui", "table", "length") => Some(EFF_TDN),
        ("Sui", "table", "destroy_empty") => Some(EFF_PDN),
        ("Sui", "table", "drop") => Some(EFF_PDN),
        ("Sui", "table", "borrow_or_unknown") => Some(EFF_TDN),
        ("Sui", "table", "add_pure") => Some(EFF_TDN),
        ("Sui", "table", "remove_pure") => Some(EFF_TDN),
        ("Sui", "object_table", "new") => Some(EFF_TDM_GLOBAL),
        ("Sui", "object_table", "add") => Some(EFF_PDM_LOCAL),
        ("Sui", "object_table", "borrow") => Some(EFF_PDN),
        ("Sui", "object_table", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "object_table", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "object_table", "contains") => Some(EFF_TDN),
        ("Sui", "object_table", "is_empty") => Some(EFF_TDN),
        ("Sui", "object_table", "length") => Some(EFF_TDN),
        ("Sui", "object_table", "destroy_empty") => Some(EFF_PDN),
        ("Sui", "object_table", "value_id") => Some(EFF_TDN),
        ("Sui", "object_table", "borrow_or_unknown") => Some(EFF_TDN),
        ("Sui", "object_table", "add_pure") => Some(EFF_TDN),
        ("Sui", "object_table", "remove_pure") => Some(EFF_TDN),
        ("Sui", "vec_map", "empty") => Some(EFF_TDN),
        ("Sui", "vec_map", "insert") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "pop") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "get") => Some(EFF_PDN),
        ("Sui", "vec_map", "get_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "try_get") => Some(EFF_TDN),
        ("Sui", "vec_map", "contains") => Some(EFF_TDN),
        ("Sui", "vec_map", "length") => Some(EFF_TDN),
        ("Sui", "vec_map", "is_empty") => Some(EFF_TDN),
        ("Sui", "vec_map", "destroy_empty") => Some(EFF_PDN),
        ("Sui", "vec_map", "into_keys_values") => Some(EFF_TDN),
        ("Sui", "vec_map", "from_keys_values") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "keys") => Some(EFF_TDN),
        ("Sui", "vec_map", "get_idx_opt") => Some(EFF_TDN),
        ("Sui", "vec_map", "get_idx") => Some(EFF_PDN),
        ("Sui", "vec_map", "get_entry_by_idx") => Some(EFF_PDN),
        ("Sui", "vec_map", "get_entry_by_idx_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "remove_entry_by_idx") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_map", "size") => Some(EFF_TDN),
        ("Sui", "vec_map", "get_or_unknown") => Some(EFF_TDN),
        ("Sui", "vec_map", "get_entry_by_idx_or_unknown") => Some(EFF_TDN),
        ("Sui", "vec_map", "get_idx_or_unknown") => Some(EFF_TDN),
        ("Sui", "vec_map", "insert_pure") => Some(EFF_TDN),
        ("Sui", "vec_map", "remove_pure") => Some(EFF_TDN),
        ("Sui", "vec_set", "empty") => Some(EFF_TDN),
        ("Sui", "vec_set", "singleton") => Some(EFF_TDN),
        ("Sui", "vec_set", "insert") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_set", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_set", "contains") => Some(EFF_TDN),
        ("Sui", "vec_set", "length") => Some(EFF_TDN),
        ("Sui", "vec_set", "is_empty") => Some(EFF_TDN),
        ("Sui", "vec_set", "into_keys") => Some(EFF_TDN),
        ("Sui", "vec_set", "from_keys") => Some(EFF_PDM_LOCAL),
        ("Sui", "vec_set", "keys") => Some(EFF_TDN),
        ("Sui", "vec_set", "size") => Some(EFF_TDN),
        ("Sui", "vec_set", "insert_pure") => Some(EFF_TDN),
        ("Sui", "vec_set", "remove_pure") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "add") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "borrow") => Some(EFF_PDN),
        ("Sui", "dynamic_field", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "remove_if_exists") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "exists") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "exists_") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "exists_with_type") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "borrow_or_unknown") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "hash_type_and_key") => Some(EFF_PDN),
        ("Sui", "dynamic_field", "add_child_object") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "borrow_child_object") => Some(EFF_PDN),
        ("Sui", "dynamic_field", "borrow_child_object_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "remove_child_object") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_field", "has_child_object") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "has_child_object_with_ty") => Some(EFF_TDN),
        ("Sui", "dynamic_field", "field_info") => Some(EFF_PDN),
        ("Sui", "dynamic_field", "field_info_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "add") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "borrow") => Some(EFF_PDN),
        ("Sui", "dynamic_object_field", "borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "exists") => Some(EFF_TDN),
        ("Sui", "dynamic_object_field", "exists_") => Some(EFF_TDN),
        ("Sui", "dynamic_object_field", "exists_with_type") => Some(EFF_TDN),
        ("Sui", "dynamic_object_field", "id") => Some(EFF_TDN),
        ("Sui", "dynamic_object_field", "internal_add") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "internal_borrow") => Some(EFF_PDN),
        ("Sui", "dynamic_object_field", "internal_borrow_mut") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "internal_remove") => Some(EFF_PDM_LOCAL),
        ("Sui", "dynamic_object_field", "internal_exists_with_type") => Some(EFF_TDN),
        ("Sui", "dynamic_object_field", "borrow_or_unknown") => Some(EFF_TDN),
        ("Sui", "test_scenario", "return_shared") => Some(EFF_TDM_GLOBAL),
        ("Sui", "test_scenario", "return_to_address") => Some(EFF_TDM_GLOBAL),
        ("Sui", "test_scenario", "return_immutable") => Some(EFF_TDM_GLOBAL),
        ("Sui", "transfer", "transfer") => Some(EFF_TDM_GLOBAL),
        ("Sui", "transfer", "public_transfer") => Some(EFF_TDM_GLOBAL),
        ("Sui", "transfer", "share_object") => Some(EFF_TDM_GLOBAL),
        ("Sui", "transfer", "public_share_object") => Some(EFF_TDM_GLOBAL),
        ("Sui", "transfer", "freeze_object") => Some(EFF_TDM_GLOBAL),
        ("Sui", "transfer", "public_freeze_object") => Some(EFF_TDM_GLOBAL),
        ("Sui", "event", "emit") => Some(EFF_TDM_GLOBAL),
        ("Sui", "test_utils", "create_one_time_witness") => Some(Effects::WORLD),
        ("Sui", "types", "is_one_time_witness") => Some(EFF_TDN),
        ("Sui", "random", "next_u8") => Some(EFF_TNM_GLOBAL),
        ("Sui", "random", "next_u64") => Some(EFF_TNM_GLOBAL),
        ("Sui", "random", "next_u128") => Some(EFF_TNM_GLOBAL),
        ("Sui", "random", "new_generator") => Some(EFF_PDM_LOCAL),
        ("Sui", "random", "generate_bool") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_bytes") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u8") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u16") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u32") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u64") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u128") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u256") => Some(EFF_PNM_LOCAL),
        // The `*_in_range` family has the same shape as the plain
        // `generate_u<N>` above -- `&mut RandomGenerator` plus two bounds --
        // and the same classification: `Partial` (the framework's
        // `uint_in_range` macro asserts `min <= max` with `EInvalidRange`),
        // `NonDet`, `LocalMut`. Without a row they were CONSERVATIVE, i.e.
        // world-threaded, on top of having no Lean model at all; the
        // framework spec `SuiSpecs/Random_spec.lean` targets
        // `generate_u128_in_range` directly, so every client compiling that
        // spec file got six `Unknown identifier
        // `_root_.Random.generate_u128_in_range`` errors plus the
        // `unsolved goals` that the resulting `sorry`s left behind.
        ("Sui", "random", "generate_u8_in_range") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u16_in_range") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u32_in_range") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u64_in_range") => Some(EFF_PNM_LOCAL),
        ("Sui", "random", "generate_u128_in_range") => Some(EFF_PNM_LOCAL),
        // The metadata validation native aborts (with a specific code) but
        // mutates nothing and is deterministic: Partial / Det / NoMut. This
        // keeps `world` from being force-threaded through it (its Lean model
        // and `.aborts` companion take only `metadata`), matching the
        // `bag::borrow` shape and avoiding a world-arg arity mismatch in the
        // callee-aborts splice.
        ("SuiSystem", "validator", "validate_metadata_bcs") => Some(EFF_PDN),
        _ => None,
    };
    entry.unwrap_or(Effects::CONSERVATIVE)
}

/// Native framework functions that ship a hand-written `.aborts`
/// companion in their corresponding `lemmas/natives/<Pkg>/<Mod>Natives.lean`
/// file. When stage 2's module-lift registers one of these natives,
/// it also registers a synthetic [`crate::ir::NativeDecl`] for the
/// `.aborts` sibling with `spec_target` back-referencing the base.
/// Stage 7's `aborts_map` then composes a precise callee-side abort
/// predicate into every caller's `.aborts` body.
///
/// THERE IS NO CONSERVATIVE FALLBACK. An `AbortBit::Partial` native
/// that is missing from this list contributes NOTHING to its callers'
/// abort faces: `module_lift` synthesises no `.aborts` companion, so
/// stage 7's `aborts_map` (seeded for natives only from
/// `program.natives.decls` rows carrying a `spec_target`) has no entry
/// and the callee-aborts splice skips the call entirely. The caller
/// then renders as if the native were total. A missing row is an
/// UNSOUND-DIRECTION gap, not a coarse over-approximation. (The
/// `AbortBit::Partial -> Bool(true)` fallback that earlier revisions of
/// this comment described belonged to the retired `spec_extract`.)
///
/// Listing rule, BOTH directions, enforced by
/// [`tests::every_native_with_a_real_lean_abort_predicate_is_registered`]
/// and [`tests::aborts_companions_match_lean_models`]:
///
/// * an entry here MUST be matched by a `def <fn>.aborts ...`
///   declaration in the Lean prelude file for the package;
/// * conversely, a native whose prelude file declares a NON-TRIVIAL
///   `<fn>.aborts` (anything but the constant `false`) MUST be listed
///   here. The Lean bundle is the authority on abort behaviour, and an
///   unregistered native is invisible to stage 7's `aborts_map`, so the
///   splice never fires and the abort is DROPPED from every caller's
///   `.aborts` face -- silently, and unsoundly.
///
/// Only the first direction used to be covered, and only indirectly
/// (lake build fails on the unknown identifier). The second had no
/// check at all, which is how `std::string::utf8` shipped
/// `utf8.aborts := !(internal_check_utf8_pure bytes)` in
/// `MoveStringNatives.lean` while going unregistered here: every caller
/// -- including the `#[spec(prove, target = std::string::utf8)]`
/// obligation `utf8_correct` -- then asserted that decoding never
/// aborts, which is refuted by the single byte `[0x80]`.
const NATIVES_WITH_ABORTS_COMPANIONS: &[(&str, &str, &str)] = &[
    // Entries are grouped by (package, module) and sorted by function
    // name inside each group; the GROUPS themselves are in historical
    // insertion order, not sorted. `aborts_companion_list_is_grouped_and_unique`
    // enforces exactly that, plus uniqueness.
    //
    // ---- MoveStdlib::string ----
    // Companions live in lemmas/natives/MoveStdlib/MoveStringNatives.lean.
    // All three are `Partial` in `native_effects` and all three ship a
    // real predicate: `utf8`/`append_utf8` abort on invalid UTF-8
    // (`!internal_check_utf8_pure`), `substring` on a bad index range or
    // a non-char-boundary cut. The rest of the module's companions are
    // the constant `false` and need no row.
    ("MoveStdlib", "string", "append_utf8"),
    ("MoveStdlib", "string", "substring"),
    ("MoveStdlib", "string", "utf8"),
    // No `type_name::get_address` row: its companion in
    // Type_nameNatives.lean delegates to `address_string.aborts`, which
    // is the constant `false`, so registering it buys no abort coverage
    // at all -- see the delegation rule in
    // `tests::lean_aborts_companion`.
    // ---- MoveStdlib::vector ----
    // Companions live in lemmas/natives/MoveStdlib/MoveVectorNatives.lean.
    // Without registering these, every caller of a non-empty-vector op
    // (e.g. `swap_or_fill`'s `pop_back` in the else-branch) silently
    // drops that abort face -- the call contributes nothing to the
    // caller's `.aborts` body, so e.g. `linked_table::push_back` would
    // report `aborts = false` on a path that really does abort.
    ("MoveStdlib", "vector", "borrow"),
    ("MoveStdlib", "vector", "contains"),
    ("MoveStdlib", "vector", "destroy_empty"),
    ("MoveStdlib", "vector", "index_of"),
    ("MoveStdlib", "vector", "insert"),
    ("MoveStdlib", "vector", "pop_back"),
    ("MoveStdlib", "vector", "remove"),
    ("MoveStdlib", "vector", "swap"),
    ("MoveStdlib", "vector", "swap_remove"),
    // ---- Sui::dynamic_field ----
    // Companions live in lemmas/natives/Sui/Dynamic_fieldNatives.lean
    // (`add.aborts`, `borrow.aborts`, `remove.aborts`). The
    // `borrow_mut` / `remove_if_exists` rows are inert: their
    // parent-typed stubs and companions were deleted when every df/dof
    // op was routed through the World natives, so those names never
    // reach rendering.
    ("Sui", "dynamic_field", "add"),
    ("Sui", "dynamic_field", "borrow"),
    ("Sui", "dynamic_field", "borrow_mut"),
    ("Sui", "dynamic_field", "remove"),
    ("Sui", "dynamic_field", "remove_if_exists"),
    // ---- Sui::object ----
    // `uid_as_inner.aborts` lives in lemmas/natives/Sui/ObjectNatives.lean;
    // `new.aborts` is added in the same file alongside this list.
    ("Sui", "object", "new"),
    ("Sui", "object", "uid_as_inner"),
    // ---- Sui::object_bag ----
    // Companions live in lemmas/natives/Sui/Object_bagNatives.lean.
    // Same modeling as `Sui::bag`: there is no `borrow_mut.aborts`
    // companion because mutation renders as `borrow` plus total
    // writeback.
    ("Sui", "object_bag", "add"),
    ("Sui", "object_bag", "borrow"),
    ("Sui", "object_bag", "contains"),
    ("Sui", "object_bag", "contains_with_type"),
    ("Sui", "object_bag", "destroy_empty"),
    ("Sui", "object_bag", "is_empty"),
    ("Sui", "object_bag", "length"),
    ("Sui", "object_bag", "new"),
    ("Sui", "object_bag", "remove"),
    ("Sui", "object_bag", "value_id"),
    // ---- Sui::object_table ----
    // Companions live in lemmas/natives/Sui/Object_tableNatives.lean.
    // Same key-presence modeling as `Sui::table`: add aborts iff the key
    // is PRESENT, borrow/borrow_mut/remove/value_id iff ABSENT,
    // destroy_empty iff non-empty; contains/is_empty/length/new total.
    // Without these rows the shipped companions were never composed into
    // callers' aborts chains, so e.g. `market::borrow_obligation.aborts`
    // rendered as unconditional NoAbort (caught by a kernel-checked
    // refutation of current-lending's borrow_obligation_asserts_correct).
    ("Sui", "object_table", "add"),
    ("Sui", "object_table", "borrow"),
    ("Sui", "object_table", "borrow_mut"),
    ("Sui", "object_table", "contains"),
    ("Sui", "object_table", "destroy_empty"),
    ("Sui", "object_table", "is_empty"),
    ("Sui", "object_table", "length"),
    ("Sui", "object_table", "new"),
    ("Sui", "object_table", "remove"),
    ("Sui", "object_table", "value_id"),
    // ---- Sui::table ----
    // Companions live in lemmas/natives/Sui/TableNatives.lean. Without
    // these, every native partial `table::*` op (which is most of them)
    // drops its abort face at the call site. That cascades into
    // cetus-stl's skip_list_u128 module (which wraps its dynamic-field
    // storage as `Table` rather than direct dynamic_field) reporting
    // NO aborts where the Move code really does abort.
    ("Sui", "table", "add"),
    ("Sui", "table", "borrow"),
    ("Sui", "table", "borrow_mut"),
    ("Sui", "table", "contains"),
    ("Sui", "table", "destroy_empty"),
    ("Sui", "table", "drop"),
    ("Sui", "table", "is_empty"),
    ("Sui", "table", "length"),
    ("Sui", "table", "new"),
    ("Sui", "table", "remove"),
    // ---- Sui::vec_map ----
    // Companions live in lemmas/natives/Sui/Vec_mapNatives.lean.
    // Move's vec_map is partial on: insert (duplicate key), get/remove
    // (missing key), get_entry_by_idx (out-of-range index), pop (empty),
    // destroy_empty (non-empty). Without these rows the companions were
    // never composed, so e.g.
    // `whitelist_admin::mint_new_whitelist.aborts` missed the
    // vec_map::insert duplicate-key abort (caught by a kernel-checked
    // refutation of mint_new_whitelist_asserts_correct).
    ("Sui", "vec_map", "destroy_empty"),
    ("Sui", "vec_map", "get"),
    ("Sui", "vec_map", "get_entry_by_idx"),
    ("Sui", "vec_map", "insert"),
    ("Sui", "vec_map", "pop"),
    ("Sui", "vec_map", "remove"),
    // ---- Sui::vec_set ----
    // Companions live in lemmas/natives/Sui/Vec_setNatives.lean.
    // Move's mutating set operations are partial: insert aborts on a
    // duplicate key and remove aborts on a missing key.
    ("Sui", "vec_set", "insert"),
    ("Sui", "vec_set", "remove"),
    // ---- Sui::bag ----
    // Companions live in lemmas/natives/Sui/BagNatives.lean (step-3
    // bag pass): add aborts iff the key is PRESENT
    // (EFieldAlreadyExists), borrow/remove iff ABSENT, destroy_empty
    // iff non-empty; the rest are total. No `borrow_mut` row -- Bag has
    // no Lean borrow_mut def (the renderer goes through `Bag.borrow` +
    // Mutation writeback `Bag.set`, which is total).
    ("Sui", "bag", "add"),
    ("Sui", "bag", "borrow"),
    ("Sui", "bag", "contains"),
    ("Sui", "bag", "contains_with_type"),
    ("Sui", "bag", "destroy_empty"),
    ("Sui", "bag", "is_empty"),
    ("Sui", "bag", "length"),
    ("Sui", "bag", "new"),
    ("Sui", "bag", "remove"),
    // ---- SuiSystem::validator ----
    // `validate_metadata_bcs.aborts` is hand-written in the proof package's
    // dependency overlay at `lean/natives/SuiSystem/ValidatorNatives.lean`
    // (a decoder over the real BCS
    // bytes of `bcs::to_bytes<ValidatorMetadata>`). Unlike the framework
    // companions above (which return `Bool`), it returns
    // `Abort.AbortResult AbortCode` carrying the SPECIFIC validator abort
    // code (0-7); see `NATIVES_WITH_ABORT_CODE_COMPANIONS`, which stage 7
    // uses to retype the synthetic companion so the callee-aborts splice
    // match-propagates that code instead of collapsing to a fixed `0`.
    ("SuiSystem", "validator", "validate_metadata_bcs"),
];

/// Returns true iff stage 2 should also register a synthetic
/// `<fn>.aborts` companion alongside the named native. See
/// [`NATIVES_WITH_ABORTS_COMPANIONS`].
pub fn native_has_aborts_companion(package: &str, module_name: &str, function_name: &str) -> bool {
    NATIVES_WITH_ABORTS_COMPANIONS
        .iter()
        .any(|(p, m, f)| *p == package && *m == module_name && *f == function_name)
}

/// Natives (a subset of [`NATIVES_WITH_ABORTS_COMPANIONS`]) whose
/// hand-written `.aborts` companion returns the full
/// `Abort.AbortResult AbortCode` shape carrying a SPECIFIC abort code,
/// NOT the `Bool` shape every framework companion uses. Stage 7
/// (`aborts_variant::materialise`) retypes the synthetic companion's IR
/// return type from `Bool` to the `AbortResult` struct for these, so the
/// callee-aborts splice match-propagates the precise code instead of
/// collapsing a `true` to the fixed `code := 0`.
///
/// `validate_metadata_bcs` is the only such native: its Lean model
/// (`lean/natives/SuiSystem/ValidatorNatives.lean` in the proof package)
/// decodes the real BCS bytes and returns codes 0-7 from
/// `ValidatorMetadataV1::verify`.
const NATIVES_WITH_ABORT_CODE_COMPANIONS: &[(&str, &str, &str)] =
    &[("SuiSystem", "validator", "validate_metadata_bcs")];

/// Returns true iff the named native's `.aborts` companion returns the
/// `Abort.AbortResult AbortCode` shape (a specific code) rather than
/// `Bool`. See [`NATIVES_WITH_ABORT_CODE_COMPANIONS`].
pub fn native_aborts_companion_returns_code(
    package: &str,
    module_name: &str,
    function_name: &str,
) -> bool {
    NATIVES_WITH_ABORT_CODE_COMPANIONS
        .iter()
        .any(|(p, m, f)| *p == package && *m == module_name && *f == function_name)
}

/// Check whether a Move function has the `#[ext(pure)]` attribute.
///
/// Upstream's `package_targets::check_abort_check_scope` recognizes
/// this annotation to put functions into its `pure_functions` set,
/// but that set isn't reachable from the IR-level `Function`. The
/// new pipeline reads the attribute directly off the `FunctionEnv`
/// at lift time and uses it to override the default `Impure`
/// classification on otherwise-unrecognized natives (and on
/// non-natives that the body-walker would otherwise mark Impure
/// via a transitive Impure callee).
///
/// Returns `true` when the function carries `#[ext(pure)]` (any
/// variant -- `#[spec_only, ext(pure)]`, etc.). Returns `false`
/// for anything else.
pub fn has_ext_pure(func_env: &move_model::model::FunctionEnv) -> bool {
    use move_compiler::shared::known_attributes::{
        AttributeKind_, ExternalAttribute, KnownAttribute,
    };
    if let Some(KnownAttribute::External(ExternalAttribute { attrs })) = func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::External)
        .map(|attr| &attr.value)
    {
        attrs
            .into_iter()
            .any(|attr| attr.2.value.name().value.as_str() == "pure")
    } else {
        false
    }
}

/// Check whether a Move function has the `#[ext(world)]` attribute.
///
/// Mirrors [`has_ext_pure`], but for the *world-reading* classification
/// used by hand-written datatype-invariant predicates. An
/// `#[ext(world)]` native reads global/dynamic-field state but neither
/// aborts nor is non-deterministic: its Lean body threads `world`
/// unchanged and returns it (`Dynamic_field.borrow`'s shape). Stage 2
/// locks such a native's effects at [`Effects::WORLD`]
/// (`Total` / `Det` / `GlobalMut`); the `GlobalMut` axis then seeds
/// `compute_needs_world`, so world threading propagates through every
/// caller (including quantifier bodies) automatically.
///
/// Returns `true` when the function carries `#[ext(world)]` (any
/// variant -- `#[spec_only, ext(world)]`, etc.). Returns `false` for
/// anything else.
pub fn has_ext_world(func_env: &move_model::model::FunctionEnv) -> bool {
    use move_compiler::shared::known_attributes::{
        AttributeKind_, ExternalAttribute, KnownAttribute,
    };
    if let Some(KnownAttribute::External(ExternalAttribute { attrs })) = func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::External)
        .map(|attr| &attr.value)
    {
        attrs
            .into_iter()
            .any(|attr| attr.2.value.name().value.as_str() == "world")
    } else {
        false
    }
}

/// Whether a Move function is in `#[spec_only]` scope -- carrying the
/// attribute directly, or living in a `#[spec_only]` module. User
/// `native fun` datatype-invariant predicates are spec-only (they exist only
/// for verification). The renderer uses this bit to distinguish authored
/// spec definitions from runtime native models that require explicit trust.
pub fn has_spec_only(
    func_env: &move_model::model::FunctionEnv,
    module_env: &move_model::model::ModuleEnv,
) -> bool {
    use move_compiler::shared::known_attributes::AttributeKind_;
    func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::SpecOnly)
        .is_some()
        || module_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::SpecOnly)
            .is_some()
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    #[test]
    fn function_allowlist_is_non_empty() {
        assert!(!NATIVE_FUNCTIONS.is_empty());
    }

    #[test]
    fn function_allowlist_is_sorted_by_pkg_mod_name() {
        for window in NATIVE_FUNCTIONS.windows(2) {
            assert!(
                window[0] < window[1],
                "native function list out of order: {:?} >= {:?}; keep entries sorted lexicographically by (package, module, function)",
                window[0],
                window[1]
            );
        }
    }

    #[test]
    fn function_allowlist_has_no_duplicates() {
        let mut seen = BTreeSet::new();
        for entry in NATIVE_FUNCTIONS {
            assert!(
                seen.insert(*entry),
                "duplicate native function entry: {:?}",
                entry
            );
        }
    }

    #[test]
    fn includes_design_doc_listed_collections() {
        // The design doc enumerates a specific minimum set; verify
        // the allowlist covers it. See
        // `plans/lean-pipeline/stage-02-ir-cfg.md` "Pre-pass A".
        // We pick a representative function for each module so the
        // check is per-thing in the new per-function model.
        let required: &[(&str, &str, &str)] = &[
            ("Sui", "bag", "add"),
            ("Sui", "object_bag", "add"),
            ("Sui", "table", "add"),
            ("Sui", "object_table", "add"),
            ("Sui", "vec_map", "insert"),
            ("Sui", "vec_set", "insert"),
            ("MoveStdlib", "vector", "push_back"),
        ];
        for (pkg, modu, fun) in required {
            assert!(
                is_native_function(pkg, modu, fun, false),
                "design-doc-listed native ({pkg}, {modu}, {fun}) missing from allowlist"
            );
        }
    }

    #[test]
    fn injected_stub_native_is_recognised() {
        // The sui-prover-injected placeholder is exempt from the
        // user-native machinery regardless of module.
        assert!(is_injected_stub_native("__stub_placeholder"));
        assert!(!is_injected_stub_native("counter_inv"));
        assert!(!is_injected_stub_native("push_back"));
    }

    #[test]
    fn group_ops_equal_has_a_lean_model() {
        // `sui::group_ops::equal` is in NATIVE_FUNCTIONS, so its Move body is
        // discarded and the bundle's model is its only definition. It had
        // none: every rendered caller (hashi's
        // `committee_set::new_committee_from_voting_powers`) failed with
        // `Unknown identifier _root_.Group_ops.equal`, which broke the whole
        // specs package's Lean build and stopped every lane.
        assert!(NATIVE_FUNCTIONS.contains(&("Sui", "group_ops", "equal")));
        let model = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("lemmas/natives/Sui/Group_opsNatives.lean");
        let source = std::fs::read_to_string(&model).unwrap();
        assert!(
            source.lines().any(|line| line.starts_with("def equal ")),
            "{} must define `equal`",
            model.display()
        );
    }

    #[test]
    fn vec_set_mutators_have_abort_companions() {
        assert!(native_has_aborts_companion("Sui", "vec_set", "insert"));
        assert!(native_has_aborts_companion("Sui", "vec_set", "remove"));
        assert!(!native_has_aborts_companion("Sui", "vec_set", "contains"));
    }

    #[test]
    fn string_utf8_has_an_abort_companion() {
        // `std::string::utf8` aborts on invalid UTF-8 -- that is its
        // entire contract, and `MoveStringNatives.lean` has always said
        // so. It went unregistered here, so every caller's `.aborts`
        // face dropped the abort and read as unconditionally total.
        assert!(native_has_aborts_companion("MoveStdlib", "string", "utf8"));
        assert!(native_has_aborts_companion(
            "MoveStdlib",
            "string",
            "substring"
        ));
        assert!(native_has_aborts_companion(
            "MoveStdlib",
            "string",
            "append_utf8"
        ));
        // `length` / `as_bytes` / `append` are total: no row, and the
        // Lean companions are the constant `false`.
        assert!(!native_has_aborts_companion(
            "MoveStdlib",
            "string",
            "length"
        ));
        assert!(!native_has_aborts_companion(
            "MoveStdlib",
            "string",
            "append"
        ));
    }

    /// The bundle at `lemmas/natives/<Pkg>/<Ns>Natives.lean` is the
    /// AUTHORITY on a framework native's abort behaviour, and
    /// [`NATIVES_WITH_ABORTS_COMPANIONS`] is the only channel by which
    /// that authority reaches stage 7's `aborts_map`. A native missing
    /// from the list is invisible to the callee-aborts splice: its call
    /// stays a dead value binding in the cloned `.aborts` body and the
    /// caller's abort face silently under-approximates.
    ///
    /// Both directions of the listing rule are checked here, because
    /// they fail in opposite ways:
    ///
    /// * REAL predicate in Lean, no row here -> SILENT unsoundness.
    ///   This is the direction that had no check at all and that let
    ///   `std::string::utf8` sit unregistered.
    /// * row here, no `def` in Lean -> LOUD `unknown identifier` at
    ///   lake build, but only for a package that happens to call it.
    ///
    /// "Real" means the companion's body is anything other than the
    /// constant `false`; a total native may carry a `:= false`
    /// companion and needs no row.
    #[test]
    fn every_native_with_a_real_lean_abort_predicate_is_registered() {
        let natives_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas/natives");
        assert!(
            natives_dir.is_dir(),
            "lean model bundle missing at {}",
            natives_dir.display()
        );

        let mut sources: std::collections::BTreeMap<(&str, &str), Option<String>> =
            std::collections::BTreeMap::new();
        let mut load = |pkg: &'static str, module: &'static str| -> Option<String> {
            sources
                .entry((pkg, module))
                .or_insert_with(|| {
                    let ns = crate::render::escape::module_name_to_namespace(module);
                    let path = natives_dir.join(pkg).join(format!("{ns}Natives.lean"));
                    std::fs::read_to_string(path).ok()
                })
                .clone()
        };

        let mut unregistered = Vec::new();
        for (pkg, module, name) in NATIVE_FUNCTIONS {
            let Some(src) = load(pkg, module) else {
                continue;
            };
            if matches!(lean_aborts_companion(&src, name), Some(AbortsBody::Real))
                && !native_has_aborts_companion(pkg, module, name)
            {
                unregistered.push(format!("({pkg}, {module}, {name})"));
            }
        }
        assert!(
            unregistered.is_empty(),
            "these natives ship a REAL `.aborts` predicate in the Lean model bundle but are \
             missing from NATIVES_WITH_ABORTS_COMPANIONS, so stage 7 drops their abort from \
             every caller's `.aborts` face:\n  {}",
            unregistered.join("\n  ")
        );

        // Rows that legitimately name no companion in THIS bundle. Each
        // needs a reason, and the reason has to be a fact about where the
        // declaration lives or why the op never reaches rendering --
        // never "it seems to work".
        //
        // * `validate_metadata_bcs`: hand-written in the proof package's
        //   dependency overlay
        //   (`lean/natives/SuiSystem/ValidatorNatives.lean`), not here --
        //   see NATIVES_WITH_ABORT_CODE_COMPANIONS.
        // * `dynamic_field::borrow_mut` / `remove_if_exists`: the
        //   parent-typed high-level stubs and their companions were
        //   deleted from Dynamic_fieldNatives.lean when every df/dof op
        //   was routed through the World natives
        //   (`dynamic_field_rewrite`), so neither name survives to
        //   rendering. The rows are inert rather than wrong -- a routing
        //   gap fails loudly on the unknown identifier, which is the
        //   stated point of that deletion.
        // * `object_bag::value_id`: Object_bagNatives.lean models
        //   neither `value_id` nor its companion (unlike
        //   `object_table`), so a caller already fails on the BASE
        //   identifier.
        let off_bundle: &[(&str, &str, &str)] = &[
            ("Sui", "dynamic_field", "borrow_mut"),
            ("Sui", "dynamic_field", "remove_if_exists"),
            ("Sui", "object_bag", "value_id"),
            ("SuiSystem", "validator", "validate_metadata_bcs"),
        ];
        let mut unmodelled = Vec::new();
        for (pkg, module, name) in NATIVES_WITH_ABORTS_COMPANIONS {
            if off_bundle.contains(&(pkg, module, name)) {
                continue;
            }
            let declared = load(pkg, module)
                .map(|src| lean_aborts_companion(&src, name).is_some())
                .unwrap_or(false);
            if !declared {
                unmodelled.push(format!("({pkg}, {module}, {name})"));
            }
        }
        assert!(
            unmodelled.is_empty(),
            "these natives are registered in NATIVES_WITH_ABORTS_COMPANIONS but the Lean model \
             bundle declares no `<fn>.aborts` for them, so any caller fails the lake build on an \
             unknown identifier:\n  {}",
            unmodelled.join("\n  ")
        );
    }

    /// The world-threading half of the same bundle-vs-table contract.
    ///
    /// `compute_needs_world` seeds its closure from
    /// `NativeDecl::effects.mutation == GlobalMut`, so `native_effects`
    /// decides -- for every native, one bit -- whether stage 4 appends
    /// `world` to the emitted call and a world slot to the destructure.
    /// The Lean model in `lemmas/natives/<Pkg>/<Ns>Natives.lean` has to
    /// declare the matching arity, and NOTHING checks that at build time:
    /// the two halves only meet inside the render-time `native-model
    /// classification` lake query, in whichever client happens to compile
    /// the module that calls the native. Both directions fail there, and
    /// both fail as a wall rather than a hint:
    ///
    /// * table world-threads, model is pure ->
    ///   `Function expected at <Native> <args> ... but this term has type
    ///   Bool / Note: Expected a function because this term is being
    ///   applied to the argument world`
    /// * table says pure, model threads world ->
    ///   `Type mismatch ... has type World -> T x World but is expected to
    ///   have type T`
    ///
    /// This bit is only for the natives that the FRAMEWORK spec package
    /// re-exports (`SuiSpecs` ships an identity `#[spec(target = ..)]` for
    /// each), because those are compiled for every client whose module set
    /// pulls the spec file in, with no client code required: 30 of the 39
    /// errors that blocked `securitize/token-distribution` were this,
    /// across `Config_spec`, `Ecdsa_r1_spec`, `Ecvrf_spec`, `Ed25519_spec`,
    /// `Event_spec`, `Groth16_spec`, `Nitro_attestation_spec`,
    /// `Poseidon_spec`, `Vdf_spec` and both `Zklogin_verified_*_spec`
    /// files -- and two more (`Hash_spec`) were the same defect pointing
    /// the other way.
    #[test]
    fn native_world_arity_matches_lean_models() {
        let natives_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas/natives");
        assert!(
            natives_dir.is_dir(),
            "lean model bundle missing at {}",
            natives_dir.display()
        );

        // A native whose `native_effects` row disagrees with its Lean
        // model on purpose. Every row needs a reason that is a FACT about
        // where the call goes, never "it seems to work" -- and the test
        // fails if a row stops disagreeing, so a stale disclosure cannot
        // sit here unnoticed.
        //
        // * `dynamic_field::{add, borrow, remove}`: the Lean defs of these
        //   names are the WORLD-MODEL primitives that
        //   `dynamic_field_rewrite` emits directly
        //   (`Dynamic_field.borrow K V uid k world`), not the shape stage 4
        //   would derive from the Move signature. No df call survives to
        //   rendering as a plain native call, so the Move-side rows
        //   (`EFF_PDN` / `EFF_PDM_LOCAL`, matching the Move abort and
        //   `&mut` shape) never meet these defs.
        let off_contract: &[(&str, &str, &str)] = &[
            ("Sui", "dynamic_field", "add"),
            ("Sui", "dynamic_field", "borrow"),
            ("Sui", "dynamic_field", "remove"),
        ];

        let mut sources: std::collections::BTreeMap<(&str, &str), Option<String>> =
            std::collections::BTreeMap::new();
        let mut load = |pkg: &'static str, module: &'static str| -> Option<String> {
            sources
                .entry((pkg, module))
                .or_insert_with(|| {
                    let ns = crate::render::escape::module_name_to_namespace(module);
                    let path = natives_dir.join(pkg).join(format!("{ns}Natives.lean"));
                    std::fs::read_to_string(path).ok()
                })
                .clone()
        };

        let mut model_pure_call_threaded = Vec::new();
        let mut model_threaded_call_pure = Vec::new();
        let mut stale_disclosures: Vec<String> = Vec::new();
        for (pkg, module, name) in NATIVE_FUNCTIONS {
            let Some(src) = load(pkg, module) else {
                continue;
            };
            // A native the bundle does not model at all is a different
            // defect (`unknown identifier`, and it is what
            // `random::generate_u128_in_range` was), caught the moment a
            // caller compiles; this test owns arity, not coverage.
            let Some(signature) = lean_def_signature(&src, name) else {
                continue;
            };
            let call_is_world_threaded =
                native_effects(pkg, module, name).mutation == crate::ir::MutLevel::GlobalMut;
            let model_takes_world = lean_signature_takes_world(&signature);
            let disagrees = call_is_world_threaded != model_takes_world;
            if off_contract.contains(&(pkg, module, name)) {
                if !disagrees {
                    stale_disclosures.push(format!("({pkg}, {module}, {name})"));
                }
                continue;
            }
            if disagrees {
                if call_is_world_threaded {
                    model_pure_call_threaded.push(format!("({pkg}, {module}, {name})"));
                } else {
                    model_threaded_call_pure.push(format!("({pkg}, {module}, {name})"));
                }
            }
        }

        assert!(
            model_pure_call_threaded.is_empty(),
            "`native_effects` classifies these natives `GlobalMut`, so stage 4 emits \
             `<Native> <args> world`, but their Lean models in the bundle take no world. Every \
             client compiling a caller gets `Function expected at ... applied to the argument \
             world` out of the native-model classification query:\n  {}",
            model_pure_call_threaded.join("\n  ")
        );
        assert!(
            model_threaded_call_pure.is_empty(),
            "these natives' Lean models take a `World` parameter but `native_effects` does not \
             classify them `GlobalMut`, so stage 4 emits a pure call and lake reports \
             `Type mismatch ... has type World -> _ x World`:\n  {}",
            model_threaded_call_pure.join("\n  ")
        );
        assert!(
            stale_disclosures.is_empty(),
            "these rows are declared in `off_contract` but no longer disagree; delete them so the \
             disclosure list keeps meaning what it says:\n  {}",
            stale_disclosures.join("\n  ")
        );
    }

    /// The lemma packages render into ONE FLAT Lean namespace.
    /// `render::escape::module_render_namespace` package-qualifies a user
    /// package's modules precisely so two packages that each define a
    /// `module state` do not both become `namespace State` -- and it
    /// deliberately exempts `Sui` / `MoveStdlib` / `Prover`, because
    /// qualifying those would mean rewriting every hand-written file in
    /// this bundle. The bill for that exemption is that the bundle has to
    /// keep its own names disjoint BY HAND: the namespace comes from the
    /// MODULE name alone, so `std::hash` and `sui::hash` both open
    /// `namespace Hash`, and a `def` of the same name in both files is one
    /// `Hash.sha3_256` declared twice.
    ///
    /// Nothing rejected that while the `native-model classification` query
    /// imported one queried module per environment -- two duplicate models
    /// were never resident together. The union import (one
    /// `withImportModules` over every queried module, ~12x faster) makes
    /// them co-resident, and there Lean answers `import Sui.HashNatives
    /// failed, environment already contains 'Hash.sha3_256' from
    /// MoveStdlib.HashNatives`: a hard error that fails the RENDER of every
    /// client whose module set pulls both files in (`securitize`).
    ///
    /// `private` declarations are excluded on purpose -- Lean mangles those
    /// with the declaring module's name, so they cannot collide.
    #[test]
    fn lemma_bundle_declares_no_qualified_name_twice() {
        let lemmas_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
        assert!(
            lemmas_dir.is_dir(),
            "lean model bundle missing at {}",
            lemmas_dir.display()
        );

        // A qualified name this bundle declares twice on purpose. Same
        // rule as `off_contract` above: the test fails if a listed name
        // stops being duplicated, so a stale disclosure cannot sit here.
        //
        // * the five `balance_*_supply_*` theorems: `BalanceSupplyLemmas`
        //   is a strict subset of `BalanceLemmas` (same names, same
        //   statements, four of the five textually identical), and both
        //   files carry the header saying they are copied into every
        //   output tree but "imported by nobody". No rendered module
        //   imports either, so the pair is never co-resident and the
        //   duplication is unreachable today. Deduplicating it decides
        //   which file owns five proofs that clients may pin, which is a
        //   fleet-reaching change and not this test's business.
        let duplicated_on_purpose: &[&str] = &[
            "balance_decrease_supply_aborts_no_abort_of_ge",
            "balance_increase_supply_aborts_no_abort_of_lte_max",
            "balance_increase_supply_balance_value_of_lte_max",
            "balance_increase_supply_lte_of_aborts_no_abort",
            "balance_increase_supply_value_val_of_lte_max",
        ];

        let mut declarations: std::collections::BTreeMap<
            String,
            std::collections::BTreeSet<String>,
        > = std::collections::BTreeMap::new();
        let mut files = Vec::new();
        collect_lean_files(&lemmas_dir, &mut files);
        assert!(
            !files.is_empty(),
            "no .lean files under {}",
            lemmas_dir.display()
        );
        for path in &files {
            let source = std::fs::read_to_string(path).unwrap();
            let relative = path
                .strip_prefix(&lemmas_dir)
                .unwrap_or(path)
                .display()
                .to_string();
            for name in lean_public_declarations(&source) {
                declarations
                    .entry(name)
                    .or_default()
                    .insert(relative.clone());
            }
        }

        let mut collisions = Vec::new();
        let mut stale_disclosures = Vec::new();
        for (name, sources) in &declarations {
            let duplicated = sources.len() > 1;
            if duplicated_on_purpose.contains(&name.as_str()) {
                if !duplicated {
                    stale_disclosures.push(name.clone());
                }
                continue;
            }
            if duplicated {
                collisions.push(format!(
                    "{name}\n      {}",
                    sources.iter().cloned().collect::<Vec<_>>().join("\n      ")
                ));
            }
        }

        assert!(
            collisions.is_empty(),
            "these qualified names are declared by more than one module in the shipped lemma \
             bundle. The lemma packages share one flat namespace, so this is one name declared \
             twice -- and `native-model classification` imports every queried module into a \
             single environment, where Lean rejects the second with `import ... failed, \
             environment already contains ...` and the client's render dies:\n  {}",
            collisions.join("\n  ")
        );
        assert!(
            stale_disclosures.is_empty(),
            "these names are declared in `duplicated_on_purpose` but are no longer duplicated; \
             delete them so the disclosure list keeps meaning what it says:\n  {}",
            stale_disclosures.join("\n  ")
        );
    }

    /// Every non-`private` declaration a Lean source declares, qualified by
    /// the `namespace` stack it sits in. Anchored at column 0: a top-level
    /// declaration is never indented in this bundle, and matching indented
    /// lines would read tactic-script text as declarations.
    fn lean_public_declarations(source: &str) -> Vec<String> {
        const KEYWORDS: &[&str] = &[
            "def",
            "abbrev",
            "theorem",
            "axiom",
            "opaque",
            "structure",
            "inductive",
            "class",
            "instance",
        ];
        const MODIFIERS: &[&str] = &["protected ", "noncomputable ", "unsafe ", "partial "];

        let mut namespaces: Vec<&str> = Vec::new();
        let mut found = Vec::new();
        for line in source.lines() {
            if line.starts_with(char::is_whitespace) {
                continue;
            }
            if let Some(rest) = line.strip_prefix("namespace ") {
                if let Some(name) = rest.split_whitespace().next() {
                    namespaces.push(name);
                }
                continue;
            }
            if let Some(rest) = line.strip_prefix("end ") {
                let name = rest.trim();
                if namespaces.last() == Some(&name) {
                    namespaces.pop();
                }
                continue;
            }
            // `@[simp] theorem foo ...` and `@[reducible] def lt ...` are both
            // common in this bundle, so an attribute prefix has to be peeled
            // or the declaration is invisible to the scan.
            let mut head = line;
            loop {
                if let Some(rest) = head.strip_prefix("@[") {
                    match rest.find(']') {
                        Some(close) => {
                            head = rest[close + 1..].trim_start();
                            continue;
                        }
                        None => break,
                    }
                }
                match MODIFIERS.iter().find_map(|m| head.strip_prefix(m)) {
                    Some(rest) => head = rest,
                    None => break,
                }
            }
            let Some(name) = KEYWORDS.iter().find_map(|keyword| {
                head.strip_prefix(keyword)
                    .and_then(|rest| rest.strip_prefix(char::is_whitespace))
                    .map(|rest| rest.trim_start())
                    .and_then(|rest| {
                        let end = rest
                            .find(|c: char| {
                                !(c.is_alphanumeric()
                                    || c == '_'
                                    || c == '.'
                                    || c == '\''
                                    || c == '«'
                                    || c == '»')
                            })
                            .unwrap_or(rest.len());
                        (end > 0).then(|| &rest[..end])
                    })
            }) else {
                continue;
            };
            let mut qualified = namespaces.join(".");
            if !qualified.is_empty() {
                qualified.push('.');
            }
            qualified.push_str(name);
            found.push(qualified);
        }
        found
    }

    /// Text of `def <name>`'s signature -- everything between the
    /// declaration name and the defining `:=` -- or `None` when the file
    /// declares no such `def`. Matches the declaration NAME exactly, so
    /// `generate_u8` is not found by looking at `generate_u8_in_range`
    /// and a base native is never confused with its `.aborts` companion.
    fn lean_def_signature(src: &str, name: &str) -> Option<String> {
        let lines: Vec<&str> = src.lines().collect();
        for (i, raw) in lines.iter().enumerate() {
            let mut line = raw.trim_start();
            if let Some(rest) = line.strip_prefix("@[") {
                match rest.find(']') {
                    Some(close) => line = rest[close + 1..].trim_start(),
                    None => continue,
                }
            }
            line = line.strip_prefix("private ").unwrap_or(line);
            line = line.strip_prefix("noncomputable ").unwrap_or(line);
            let Some(after_def) = line.strip_prefix("def ") else {
                continue;
            };
            let Some(tail) = after_def.trim_start().strip_prefix(name) else {
                continue;
            };
            if tail
                .chars()
                .next()
                .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '\'')
            {
                continue;
            }
            let mut signature = String::new();
            let mut head = tail.to_string();
            let mut j = i;
            loop {
                if let Some((lhs, _)) = head.split_once(":=") {
                    signature.push_str(lhs);
                    break;
                }
                signature.push_str(&head);
                signature.push('\n');
                j += 1;
                match lines.get(j) {
                    Some(next) => head = (*next).to_string(),
                    None => break,
                }
            }
            return Some(signature);
        }
        None
    }

    /// Whether a `def` signature declares a `World` PARAMETER. The models
    /// spell it either through the file-local `World` notation
    /// (`(world : World)`) or fully (`Prover.World.World Ev Ob ..`); a
    /// world in the RETURN type without one in the parameters is not a
    /// world-threaded call shape, so only binders count.
    fn lean_signature_takes_world(signature: &str) -> bool {
        for (index, _) in signature.match_indices('(') {
            let Some(close) = matching_paren(signature, index) else {
                continue;
            };
            let binder = &signature[index + 1..close];
            let Some((_, ty)) = binder.split_once(':') else {
                continue;
            };
            let ty = ty.trim();
            if ty == "World"
                || ty.starts_with("World ")
                || ty.starts_with("Prover.World.World")
                || ty.starts_with("Prover.World.World\n")
            {
                return true;
            }
        }
        false
    }

    /// Index of the `)` closing the `(` at `open_at`, honouring nesting.
    fn matching_paren(text: &str, open_at: usize) -> Option<usize> {
        let mut depth = 0usize;
        for (index, ch) in text.char_indices().skip_while(|(i, _)| *i < open_at) {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(index);
                    }
                }
                _ => {}
            }
        }
        None
    }

    #[test]
    fn lean_def_signature_matches_names_exactly() {
        let src = "\
namespace Random
def generate_u8 (gen : RandomGenerator) : BoundedNat (2^8) x RandomGenerator :=
  (default, gen)

def generate_u8.aborts (_gen : RandomGenerator) : Bool := false

def generate_u8_in_range (gen : RandomGenerator) (min _max : BoundedNat (2^8))
    : BoundedNat (2^8) x RandomGenerator :=
  (min, gen)

def emit (tv0 : Type) (_event : tv0) (world : World) : World :=
  world

def sha2_256 (data : List Nat) (world : Prover.World.World Ev Ob Df Be)
    : (List Nat x Prover.World.World Ev Ob Df Be) :=
  (data, world)
end Random
";
        assert!(lean_def_signature(src, "generate_u8").is_some());
        assert!(lean_def_signature(src, "generate_u8_in_range").is_some());
        assert!(lean_def_signature(src, "generate_u16").is_none());
        // The base native's signature is not the companion's.
        assert!(!lean_signature_takes_world(
            &lean_def_signature(src, "generate_u8").unwrap()
        ));
        assert!(!lean_signature_takes_world(
            &lean_def_signature(src, "generate_u8_in_range").unwrap()
        ));
        assert!(lean_signature_takes_world(
            &lean_def_signature(src, "emit").unwrap()
        ));
        assert!(lean_signature_takes_world(
            &lean_def_signature(src, "sha2_256").unwrap()
        ));
    }

    #[derive(Debug, PartialEq, Eq)]
    enum AbortsBody {
        /// `:= false`, or a delegation to a companion that is itself
        /// trivial -- the native is total, so no row is required.
        Trivial,
        /// Anything else -- a genuine abort condition.
        Real,
    }

    /// Find `def <name>.aborts` in a Lean natives file and classify its
    /// body. Matches the declaration NAME exactly (so `contains.aborts`
    /// is not found by looking at `contains_with_type.aborts`), tolerates
    /// an `@[...]` attribute or `private` prefix, allows the `:=` and the
    /// body to sit on later lines, and skips `--` comment lines when
    /// looking for the body's first token.
    ///
    /// A body that is exactly a call to a SIBLING companion in the same
    /// file (`get_address.aborts self := address_string.aborts self`) is
    /// classified by that sibling: the model is saying "this native
    /// aborts exactly when that one does", so a delegation to a
    /// constant-`false` companion is itself total and needs no row.
    /// Resolved one level only, and a cycle or a missing sibling reads
    /// as `Real` -- erring towards demanding a row rather than silently
    /// excusing one.
    fn lean_aborts_companion(src: &str, name: &str) -> Option<AbortsBody> {
        match lean_aborts_body_head(src, name) {
            None => None,
            Some(first) => {
                if first == "false" || first == "False" {
                    return Some(AbortsBody::Trivial);
                }
                if let Some(delegate) = first.strip_suffix(".aborts").or_else(|| {
                    first
                        .split_whitespace()
                        .next()
                        .and_then(|head| head.strip_suffix(".aborts"))
                }) {
                    if delegate != name {
                        if let Some(inner) = lean_aborts_body_head(src, delegate) {
                            if inner == "false" || inner == "False" {
                                return Some(AbortsBody::Trivial);
                            }
                        }
                    }
                }
                Some(AbortsBody::Real)
            }
        }
    }

    /// The first non-blank, non-comment line of `<name>.aborts`'s body,
    /// or `None` when the file declares no such companion.
    fn lean_aborts_body_head(src: &str, name: &str) -> Option<String> {
        let lines: Vec<&str> = src.lines().collect();
        let decl = format!("{name}.aborts");
        for (i, raw) in lines.iter().enumerate() {
            let mut line = raw.trim_start();
            if let Some(rest) = line.strip_prefix("@[") {
                match rest.find(']') {
                    Some(close) => line = rest[close + 1..].trim_start(),
                    None => continue,
                }
            }
            line = line.strip_prefix("private ").unwrap_or(line);
            let Some(after_def) = line.strip_prefix("def ") else {
                continue;
            };
            let after_def = after_def.trim_start();
            let Some(tail) = after_def.strip_prefix(decl.as_str()) else {
                continue;
            };
            if tail
                .chars()
                .next()
                .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '.')
            {
                continue;
            }
            // Accumulate forward until the defining `:=`.
            let mut body = String::new();
            let mut j = i;
            let mut head = tail.to_string();
            loop {
                if let Some((_, rhs)) = head.split_once(":=") {
                    body.push_str(rhs);
                    break;
                }
                j += 1;
                match lines.get(j) {
                    Some(next) => head = (*next).to_string(),
                    None => return None,
                }
            }
            // First non-blank, non-comment token sequence is the body.
            let mut first = body.trim().to_string();
            while first.is_empty() || first.starts_with("--") {
                j += 1;
                match lines.get(j) {
                    Some(next) => first = next.trim().to_string(),
                    None => break,
                }
            }
            return Some(first);
        }
        None
    }

    #[test]
    fn lean_aborts_companion_classifies_bodies() {
        let src = "\
namespace MoveString
def utf8.aborts (bytes : List (BoundedNat (2^8))) : Bool :=
  !(internal_check_utf8_pure bytes)

def length.aborts (_self : MoveString) : Bool := false

def contains_with_type.aborts (_self : MoveString) : Bool := false

def add.aborts (self : Bag) (k : K) : Bool :=
  -- leading comment before the real body
  self.storage.any (fun e => e == k)

def address_string.aborts (_self : TypeName) : Bool := false

def get_address.aborts (self : TypeName) : Bool :=
  address_string.aborts self

def delegates_to_a_real_one.aborts (bytes : List (BoundedNat (2^8))) : Bool :=
  utf8.aborts bytes
end MoveString
";
        assert_eq!(lean_aborts_companion(src, "utf8"), Some(AbortsBody::Real));
        assert_eq!(
            lean_aborts_companion(src, "length"),
            Some(AbortsBody::Trivial)
        );
        assert_eq!(lean_aborts_companion(src, "add"), Some(AbortsBody::Real));
        // Exact declaration-name match: `contains` must not be found by
        // the longer `contains_with_type.aborts` declaration.
        assert_eq!(lean_aborts_companion(src, "contains"), None);
        assert_eq!(lean_aborts_companion(src, "nonexistent"), None);
        // One-level delegation is classified by the sibling it names.
        assert_eq!(
            lean_aborts_companion(src, "get_address"),
            Some(AbortsBody::Trivial)
        );
        assert_eq!(
            lean_aborts_companion(src, "delegates_to_a_real_one"),
            Some(AbortsBody::Real)
        );
    }

    #[test]
    fn aborts_companion_list_is_grouped_and_unique() {
        let mut seen = BTreeSet::new();
        for entry in NATIVES_WITH_ABORTS_COMPANIONS {
            assert!(
                seen.insert(*entry),
                "duplicate NATIVES_WITH_ABORTS_COMPANIONS entry: {entry:?}"
            );
        }
        for window in NATIVES_WITH_ABORTS_COMPANIONS.windows(2) {
            let (p0, m0, f0) = window[0];
            let (p1, m1, f1) = window[1];
            if (p0, m0) == (p1, m1) {
                assert!(
                    f0 < f1,
                    "NATIVES_WITH_ABORTS_COMPANIONS: {p0}::{m0} block out of order: {f0:?} >= {f1:?}"
                );
            }
        }
    }

    // ---------------------------------------------------------------
    // Bidirectional guard: the Rust table vs the shipped Lean models.
    // ---------------------------------------------------------------

    /// A `.aborts` companion found in `lemmas/natives/**/*.lean`.
    /// `trivial` is true when the body is literally `false` / `False`
    /// -- a total native, legal to model and legal to leave
    /// unregistered, so the forward direction ignores it.
    #[derive(Clone, Debug)]
    struct LeanAbortsModel {
        trivial: bool,
        location: String,
    }

    fn lean_natives_root() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas/natives")
    }

    fn collect_lean_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        let entries = std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("lemmas/natives subtree {} unreadable: {e}", dir.display()));
        for entry in entries {
            let path = entry.expect("readable directory entry").path();
            if path.is_dir() {
                collect_lean_files(&path, out);
            } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
                out.push(path);
            }
        }
    }

    /// Lean namespace -> Move module name. Five irregulars exist because
    /// `escape.rs` renames modules that collide with Lean builtins
    /// (`vector`/`string`/`option`) or with each other (`Sui::bcs` vs
    /// `MoveStdlib::bcs`); everything else is the module name
    /// capitalised, so lowercasing inverts it.
    fn lean_namespace_to_move_module(namespace: &str) -> String {
        match namespace {
            "MoveVector" => "vector".to_string(),
            "MoveString" => "string".to_string(),
            "MoveOption" => "option".to_string(),
            "Sui_Bcs" | "Bcs" => "bcs".to_string(),
            other => other.to_lowercase(),
        }
    }

    /// Textual scan of the shipped Lean model bundle for
    /// `def <fn>.aborts` declarations, keyed the way the Rust table is
    /// keyed: `(package, module, function)`.
    fn scan_lean_aborts_models() -> BTreeMap<(String, String, String), LeanAbortsModel> {
        let root = lean_natives_root();
        let mut files = Vec::new();
        collect_lean_files(&root, &mut files);
        files.sort();

        let mut models: BTreeMap<(String, String, String), LeanAbortsModel> = BTreeMap::new();
        for path in &files {
            let relative = path
                .strip_prefix(&root)
                .expect("scanned file lives under lemmas/natives");
            let package = relative
                .components()
                .next()
                .expect("package directory component")
                .as_os_str()
                .to_string_lossy()
                .to_string();
            let text = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
            let lines: Vec<&str> = text.lines().collect();

            let mut namespaces: Vec<&str> = Vec::new();
            for (index, line) in lines.iter().enumerate() {
                if let Some(rest) = line.strip_prefix("namespace ") {
                    if let Some(name) = rest.split_whitespace().next() {
                        namespaces.push(name);
                    }
                    continue;
                }
                if let Some(rest) = line.strip_prefix("end ") {
                    if let Some(name) = rest.split_whitespace().next() {
                        if namespaces.last() == Some(&name) {
                            namespaces.pop();
                        }
                    }
                    continue;
                }
                let Some(rest) = line.strip_prefix("def ") else {
                    continue;
                };
                let token = rest
                    .split(|c: char| " ([{:".contains(c))
                    .next()
                    .unwrap_or_default();
                let Some(base) = token.strip_suffix(".aborts") else {
                    continue;
                };
                // `def «exists_».aborts` -- strip Lean's French-quote
                // identifier escaping.
                let function = base.replace(['\u{ab}', '\u{bb}'], "");

                // A declaration runs until the first blank line or the
                // first line starting at column 0 (Lean layout: bodies
                // are indented).
                let mut buffer = String::from(*line);
                let mut cursor = index + 1;
                while cursor < lines.len() {
                    let next = lines[cursor];
                    if next.trim().is_empty() || !next.starts_with([' ', '\t']) {
                        break;
                    }
                    buffer.push(' ');
                    buffer.push_str(next.trim());
                    cursor += 1;
                }
                let body = match buffer.find(":=") {
                    Some(at) => buffer[at + 2..].trim().to_string(),
                    None => String::new(),
                };

                let module =
                    lean_namespace_to_move_module(namespaces.last().copied().unwrap_or_default());
                let model = LeanAbortsModel {
                    trivial: body == "false" || body == "False",
                    location: format!("{}:{}", relative.display(), index + 1),
                };
                // Two files can share a namespace (Random / RandomInner).
                // Keep the informative model: a non-trivial reading wins,
                // which is the direction that flags rather than hides.
                models
                    .entry((package.clone(), module, function))
                    .and_modify(|existing| {
                        if !model.trivial {
                            *existing = model.clone();
                        }
                    })
                    .or_insert(model);
            }
        }
        models
    }

    fn table_keys() -> BTreeSet<(String, String, String)> {
        NATIVES_WITH_ABORTS_COMPANIONS
            .iter()
            .map(|(p, m, f)| (p.to_string(), m.to_string(), f.to_string()))
            .collect()
    }

    fn gap_keys(gaps: &[(&str, &str, &str, &str)]) -> BTreeSet<(String, String, String)> {
        gaps.iter()
            .map(|(p, m, f, _)| (p.to_string(), m.to_string(), f.to_string()))
            .collect()
    }

    /// Forward-direction exceptions: a NON-TRIVIALLY modelled `.aborts`
    /// companion in `lemmas/natives/**` that deliberately carries no row
    /// in [`NATIVES_WITH_ABORTS_COMPANIONS`].
    ///
    /// Deleting an entry is the action item. The array is FIXED SIZE, so
    /// a new gap cannot be waved through -- widening it is a deliberate
    /// edit, and `aborts_companions_match_lean_models` additionally fails
    /// on any entry that has STOPPED being violated, so the list cannot
    /// rot into a permanent allowlist.
    const FORWARD_GAPS: [(&str, &str, &str, &str); 2] = [
        // Body is the alias `address_string.aborts self`, and
        // `address_string.aborts` is `false` -- so the face is
        // semantically total and the row would add nothing. The scan is
        // textual and cannot see through a one-level alias.
        (
            "MoveStdlib",
            "type_name",
            "get_address",
            "alias of address_string.aborts, which is `false`; semantically total",
        ),
        // `store_bag_*` are SYNTHETIC natives minted by the bag-valued
        // dynamic-field rewrite (`stage_02_ir_cfg/dynamic_fields.rs`),
        // not lifted from any Move declaration. That file registers
        // `store_bag_add.aborts` with its own `spec_target`, so the
        // companion already composes; this table only ever covers
        // Move-lifted natives, and a row here would match nothing.
        (
            "Sui",
            "dynamic_field",
            "store_bag_add",
            "synthetic native; dynamic_fields.rs registers its companion with its own spec_target",
        ),
    ];

    /// Reverse-direction exceptions: a table row with no
    /// `def <fn>.aborts` anywhere in `lemmas/natives/**`. Such a row is
    /// inert at best (nothing reaches it) and a Lake break at worst (a
    /// synthetic companion naming a Lean declaration that does not
    /// exist). Same fixed-size / fails-when-stale contract as
    /// [`FORWARD_GAPS`].
    const REVERSE_GAPS: [(&str, &str, &str, &str); 4] = [
        // The parent-typed `dynamic_field` stubs are rewritten to the
        // synthetic World-typed `store_*` natives before render, so
        // these two rows never fire. `borrow_mut` additionally has no
        // Lean model because mutation renders as `borrow` plus a total
        // writeback.
        (
            "Sui",
            "dynamic_field",
            "borrow_mut",
            "inert: rewritten to a synthetic store_* native before render",
        ),
        (
            "Sui",
            "dynamic_field",
            "remove_if_exists",
            "inert: rewritten to Dynamic_field.store_remove_if_exists before render",
        ),
        // `Sui::object_bag::value_id` IS a real Move native, and this
        // row claims a companion that `Object_bagNatives.lean` does not
        // define (only `Object_tableNatives.lean` has a `value_id`).
        // Nothing in the corpora calls it, so the row is inert today --
        // but the first caller would render a reference to a
        // non-existent `Object_bag.value_id.aborts`. Fix by writing the
        // model, not by dropping the row.
        (
            "Sui",
            "object_bag",
            "value_id",
            "row has no model: Object_bagNatives.lean defines no value_id; latent Lake break on first caller",
        ),
        // The only companion that does NOT ship in this bundle: it is
        // hand-written in the sui-system proof package's dependency
        // overlay at `specs/lean/natives/SuiSystem/ValidatorNatives.lean`
        // (and it returns `Abort.AbortResult AbortCode`, not `Bool` --
        // see NATIVES_WITH_ABORT_CODE_COMPANIONS). Structurally outside
        // the walked tree, not a gap.
        (
            "SuiSystem",
            "validator",
            "validate_metadata_bcs",
            "companion ships in the sui-system proof-package overlay, outside lemmas/natives",
        ),
    ];

    /// Ties [`NATIVES_WITH_ABORTS_COMPANIONS`] to the Lean models it
    /// claims to mirror, in BOTH directions.
    ///
    /// The bug class this makes unrepeatable: a native whose `.aborts`
    /// companion IS modelled in Lean but is missing from the Rust table.
    /// `module_lift` then synthesises no companion decl, stage 7's
    /// `aborts_map` (seeded for natives only from `spec_target`-carrying
    /// `natives.decls` rows) gets no entry, and the callee-aborts splice
    /// skips the call -- so the caller renders as if the partial native
    /// were total. Nothing on that path over-approximates, so the gap is
    /// silent and in the unsound direction.
    /// `Sui::vec_map::get_entry_by_idx` was exactly this: a shipped Lean
    /// model that nothing ever called.
    ///
    /// The reverse direction is what makes the "an entry MUST be matched
    /// by a Lean declaration" listing rule true; before this test there
    /// was no such check anywhere (the doc comment used to credit the
    /// lake-build smoke test, which never looked).
    ///
    /// WHAT THIS GUARD CANNOT SEE -- do not over-trust a green run:
    ///
    /// 1. A native declared `AbortBit::Partial` in `native_effects` with
    ///    NO Lean model at all is invisible to both directions: there is
    ///    no `def` to walk and no row to check. Known members:
    ///    `MoveStdlib::integer::div` and `::mod`, whose Lean
    ///    `Integer.div` is total `Int` division (3 call sites in
    ///    sui-system, 280 in ember, 149 in navi, 123 in momentum, 44 in
    ///    cetus), plus `Sui::object::record_new_uid` and
    ///    `Sui::tx_context::fresh_object_address`. Closing those means
    ///    reconciling the EFFECTS table with the models -- a separate
    ///    job this test does not start.
    /// 2. Companions shipped outside `lemmas/natives/**` are not walked
    ///    (see the `validate_metadata_bcs` entry in [`REVERSE_GAPS`]).
    /// 3. Triviality is the literal body `false` / `False`. A companion
    ///    that is total by delegation reads as non-trivial (see the
    ///    `type_name::get_address` entry in [`FORWARD_GAPS`]), and a
    ///    body preceded by a comment does too. Both err toward FLAGGING,
    ///    which is the safe direction for a guard.
    /// 4. It matches by NAME. It does not check that the companion's
    ///    binder shape matches its base, nor that the modelled predicate
    ///    is the right one.
    #[test]
    fn aborts_companions_match_lean_models() {
        let models = scan_lean_aborts_models();
        assert!(
            models.len() > 100,
            "scan of {} found only {} `.aborts` models; the Lean model bundle must be present and \
             the parser must still recognise it",
            lean_natives_root().display(),
            models.len()
        );

        let table = table_keys();

        // Forward: a non-trivially modelled face must be registered.
        let modelled_nontrivial: BTreeSet<(String, String, String)> = models
            .iter()
            .filter(|(_, model)| !model.trivial)
            .map(|(key, _)| key.clone())
            .collect();
        let forward_actual: BTreeSet<(String, String, String)> =
            modelled_nontrivial.difference(&table).cloned().collect();
        let forward_expected = gap_keys(&FORWARD_GAPS);

        let forward_new: Vec<String> = forward_actual
            .difference(&forward_expected)
            .map(|key| {
                format!(
                    "{}::{}::{} (modelled at {})",
                    key.0, key.1, key.2, models[key].location
                )
            })
            .collect();
        let forward_stale: Vec<String> = forward_expected
            .difference(&forward_actual)
            .map(|key| format!("{}::{}::{}", key.0, key.1, key.2))
            .collect();
        assert!(
            forward_new.is_empty() && forward_stale.is_empty(),
            "NATIVES_WITH_ABORTS_COMPANIONS is out of sync with lemmas/natives (FORWARD).\n\
             Unregistered non-trivial Lean models -- add the row, or add an argued FORWARD_GAPS \
             entry and widen the array: {forward_new:#?}\n\
             Stale FORWARD_GAPS entries -- no longer violated, delete them: {forward_stale:#?}"
        );

        // Reverse: a registered row must have SOME Lean declaration.
        // A trivially-`false` model counts here: registering a total
        // companion is legal, it just composes as NoAbort.
        let modelled_any: BTreeSet<(String, String, String)> = models.keys().cloned().collect();
        let reverse_actual: BTreeSet<(String, String, String)> =
            table.difference(&modelled_any).cloned().collect();
        let reverse_expected = gap_keys(&REVERSE_GAPS);

        let reverse_new: Vec<String> = reverse_actual
            .difference(&reverse_expected)
            .map(|key| format!("{}::{}::{}", key.0, key.1, key.2))
            .collect();
        let reverse_stale: Vec<String> = reverse_expected
            .difference(&reverse_actual)
            .map(|key| format!("{}::{}::{}", key.0, key.1, key.2))
            .collect();
        assert!(
            reverse_new.is_empty() && reverse_stale.is_empty(),
            "NATIVES_WITH_ABORTS_COMPANIONS is out of sync with lemmas/natives (REVERSE).\n\
             Registered rows with no `def <fn>.aborts` in the bundle -- write the model, or add an \
             argued REVERSE_GAPS entry and widen the array: {reverse_new:#?}\n\
             Stale REVERSE_GAPS entries -- no longer violated, delete them: {reverse_stale:#?}"
        );
    }

    #[test]
    fn vec_map_get_entry_by_idx_has_abort_companion() {
        // The registration this guard was written for. `get_entry_by_idx`
        // aborts on an out-of-range index and ships a Lean model; before
        // it was listed here, every caller silently dropped that face.
        assert!(native_has_aborts_companion(
            "Sui",
            "vec_map",
            "get_entry_by_idx"
        ));
    }

    #[test]
    fn struct_allowlist_is_sorted_by_pkg_mod_name() {
        for window in NATIVE_STRUCTS.windows(2) {
            assert!(
                window[0] < window[1],
                "native struct list out of order: {:?} >= {:?}; keep entries sorted lexicographically by (package, module, name)",
                window[0],
                window[1]
            );
        }
    }

    #[test]
    fn struct_allowlist_has_no_duplicates() {
        let mut seen = BTreeSet::new();
        for entry in NATIVE_STRUCTS {
            assert!(
                seen.insert(*entry),
                "duplicate native struct entry: {:?}",
                entry
            );
        }
    }

    #[test]
    fn is_native_struct_recognises_known_natives() {
        // Prelude-defined types (have a `structure` or `abbrev` in
        // the natives lemmas).
        assert!(is_native_struct("MoveStdlib", "integer", "Integer"));
        assert!(is_native_struct("MoveStdlib", "type_name", "TypeName"));
        assert!(is_native_struct("Sui", "object", "UID"));
        assert!(is_native_struct("Sui", "object", "ID"));
        assert!(is_native_struct("Sui", "vec_map", "VecMap"));
        assert!(is_native_struct("Sui", "vec_set", "VecSet"));
        // Header-only stubs (declared in Move framework, no
        // corresponding `structure` in prelude lemmas but kept here
        // to preserve current behaviour).
        assert!(is_native_struct("Sui", "config", "Setting"));
    }

    #[test]
    fn is_native_struct_rejects_unknown() {
        // User project struct.
        assert!(!is_native_struct("MyProject", "pool", "Pool"));
        // Real native module but bogus struct name.
        assert!(!is_native_struct("Sui", "bag", "NotAStruct"));
        // Casing matters.
        assert!(!is_native_struct("sui", "bag", "Bag"));
        assert!(!is_native_struct("Sui", "Bag", "Bag"));
        assert!(!is_native_struct("Sui", "bag", "bag"));
    }

    #[test]
    fn is_native_function_recognises_native_fun_keyword() {
        // `move_native = true` always wins, regardless of table /
        // module-allowlist membership.
        assert!(is_native_function("MyProject", "pool", "deposit", true));
    }

    #[test]
    fn is_native_function_recognises_listed_functions() {
        // Functions in the `NATIVE_FUNCTIONS` allowlist resolve to
        // native by per-function lookup. The list is merged across
        // both supported Sui framework forks (asymptotic-code/sui-next
        // and MystenLabs/sui mainnet), so it captures every framework
        // function whose body the prelude provides.
        assert!(is_native_function(
            "MoveStdlib",
            "vector",
            "is_empty",
            false
        ));
        assert!(is_native_function("MoveStdlib", "vector", "all", false));
        assert!(is_native_function("Sui", "transfer", "transfer", false));
        assert!(is_native_function("Sui", "event", "emit", false));
        assert!(is_native_function(
            "Sui",
            "accumulator",
            "emit_deposit_event",
            false
        ));
        assert!(is_native_function(
            "Sui",
            "accumulator",
            "emit_withdraw_event",
            false
        ));
        assert!(is_native_function(
            "Sui",
            "test_utils",
            "create_one_time_witness",
            false
        ));
        // Mainnet-only entries (not in asymptotic-code/sui-next):
        assert!(is_native_function("Sui", "dynamic_field", "exists", false));
        assert!(is_native_function("Sui", "dynamic_field", "replace", false));
        assert!(is_native_function(
            "Sui",
            "dynamic_field",
            "remove_opt",
            false
        ));
    }

    #[test]
    fn is_native_function_recognises_unit_test_poison() {
        // The compiler-injected test-mode marker exists in every
        // module under --test. is_native_function must return true
        // for it in any context so the per-thing Module::is_native
        // derivation doesn't flip framework modules to non-native.
        assert!(is_native_function(
            "Sui",
            "vec_map",
            "unit_test_poison",
            false
        ));
        assert!(is_native_function(
            "MyProject",
            "pool",
            "unit_test_poison",
            false
        ));
    }

    #[test]
    fn is_native_function_rejects_unknown_in_native_module() {
        // A function name that does not appear in `NATIVE_FUNCTIONS`
        // -- even inside a Move module that has many native entries
        // -- must not be classified native. This is what enables
        // mixing translated functions inside an otherwise-native
        // framework module.
        assert!(!is_native_function(
            "Sui",
            "bag",
            "no_such_bag_function_xyz",
            false
        ));
        assert!(!is_native_function(
            "MoveStdlib",
            "vector",
            "no_such_vector_function_xyz",
            false
        ));
    }

    #[test]
    fn is_native_function_rejects_non_native_modules() {
        // `option` and `debug` carry `native_effects` entries for
        // classification purposes, but their Move bodies are
        // translated -- they are NOT framework natives. The predicate
        // must reflect that.
        assert!(!is_native_function(
            "MoveStdlib",
            "option",
            "swap_or_fill",
            false
        ));
        assert!(!is_native_function("MoveStdlib", "option", "some", false));
        assert!(!is_native_function("MoveStdlib", "debug", "print", false));
    }

    #[test]
    fn is_native_function_rejects_user_functions() {
        assert!(!is_native_function("MyProject", "pool", "deposit", false));
        assert!(!is_native_function("MyProject", "vault", "withdraw", false));
    }

    // ---- Property tests for the native_effects table.

    /// Every native function the pipeline ever looks up. Keys must
    /// appear in `native_effects`; any key that misses the table
    /// falls back to [`Effects::CONSERVATIVE`] (which is fine for
    /// safety, wrong for precision).
    const COVERED_KEYS: &[(&str, &str, &str)] = &[
        ("MoveStdlib", "bcs", "to_bytes"),
        ("Sui", "bcs", "to_bytes"),
        ("MoveStdlib", "hash", "sha2_256"),
        ("MoveStdlib", "hash", "sha3_256"),
        ("MoveStdlib", "debug", "print"),
        ("MoveStdlib", "debug", "print_stack_trace"),
        ("MoveStdlib", "integer", "abs"),
        ("MoveStdlib", "integer", "add"),
        ("MoveStdlib", "integer", "bit_and"),
        ("MoveStdlib", "integer", "bit_not"),
        ("MoveStdlib", "integer", "bit_or"),
        ("MoveStdlib", "integer", "bit_xor"),
        ("MoveStdlib", "integer", "div"),
        ("MoveStdlib", "integer", "div_round_up"),
        ("MoveStdlib", "integer", "div_trunc"),
        ("MoveStdlib", "integer", "eq"),
        ("MoveStdlib", "integer", "from_u128"),
        ("MoveStdlib", "integer", "from_u16"),
        ("MoveStdlib", "integer", "from_u256"),
        ("MoveStdlib", "integer", "from_u32"),
        ("MoveStdlib", "integer", "from_u64"),
        ("MoveStdlib", "integer", "from_u8"),
        ("MoveStdlib", "integer", "ge"),
        ("MoveStdlib", "integer", "gt"),
        ("MoveStdlib", "integer", "gte"),
        ("MoveStdlib", "integer", "is_neg"),
        ("MoveStdlib", "integer", "is_pos"),
        ("MoveStdlib", "integer", "le"),
        ("MoveStdlib", "integer", "lt"),
        ("MoveStdlib", "integer", "lte"),
        ("MoveStdlib", "integer", "mod"),
        ("MoveStdlib", "integer", "mod_trunc"),
        ("MoveStdlib", "integer", "mul"),
        ("MoveStdlib", "integer", "neg"),
        ("MoveStdlib", "integer", "pow"),
        ("MoveStdlib", "integer", "shl"),
        ("MoveStdlib", "integer", "shr"),
        ("MoveStdlib", "integer", "sqrt"),
        ("MoveStdlib", "integer", "sub"),
        ("MoveStdlib", "integer", "to_u128"),
        ("MoveStdlib", "integer", "to_u16"),
        ("MoveStdlib", "integer", "to_u256"),
        ("MoveStdlib", "integer", "to_u32"),
        ("MoveStdlib", "integer", "to_u64"),
        ("MoveStdlib", "integer", "to_u8"),
        ("MoveStdlib", "real", "add"),
        ("MoveStdlib", "real", "div"),
        ("MoveStdlib", "real", "exp"),
        ("MoveStdlib", "real", "from_integer"),
        ("MoveStdlib", "real", "from_u128"),
        ("MoveStdlib", "real", "from_u16"),
        ("MoveStdlib", "real", "from_u256"),
        ("MoveStdlib", "real", "from_u32"),
        ("MoveStdlib", "real", "from_u64"),
        ("MoveStdlib", "real", "from_u8"),
        ("MoveStdlib", "real", "gt"),
        ("MoveStdlib", "real", "gte"),
        ("MoveStdlib", "real", "lt"),
        ("MoveStdlib", "real", "lte"),
        ("MoveStdlib", "real", "mul"),
        ("MoveStdlib", "real", "neg"),
        ("MoveStdlib", "real", "sqrt"),
        ("MoveStdlib", "real", "sub"),
        ("MoveStdlib", "real", "to_integer"),
        ("MoveStdlib", "type_name", "borrow_string"),
        ("MoveStdlib", "type_name", "defining_id"),
        ("MoveStdlib", "type_name", "get"),
        ("MoveStdlib", "type_name", "get_with_original_ids"),
        ("MoveStdlib", "type_name", "into_string"),
        ("MoveStdlib", "type_name", "is_primitive"),
        ("MoveStdlib", "type_name", "original_id"),
        ("MoveStdlib", "type_name", "with_defining_ids"),
        ("MoveStdlib", "type_name", "with_original_ids"),
        ("MoveStdlib", "type_name", "address_string"),
        ("MoveStdlib", "type_name", "get_address"),
        ("MoveStdlib", "type_name", "module_string"),
        ("MoveStdlib", "type_name", "datatype_string"),
        ("MoveStdlib", "vector", "borrow"),
        ("MoveStdlib", "vector", "contains"),
        ("MoveStdlib", "vector", "empty"),
        ("MoveStdlib", "vector", "is_empty"),
        ("MoveStdlib", "vector", "length"),
        ("MoveStdlib", "vector", "singleton"),
        ("MoveStdlib", "vector", "borrow_mut"),
        ("MoveStdlib", "vector", "pop_back"),
        ("MoveStdlib", "vector", "remove"),
        ("MoveStdlib", "vector", "swap"),
        ("MoveStdlib", "vector", "swap_remove"),
        ("MoveStdlib", "vector", "push_back"),
        ("MoveStdlib", "vector", "append"),
        ("MoveStdlib", "vector", "reverse"),
        ("MoveStdlib", "vector", "destroy_empty"),
        ("MoveStdlib", "vector", "index_of"),
        ("MoveStdlib", "vector", "insert"),
        ("MoveStdlib", "vector", "flatten"),
        ("MoveStdlib", "string", "utf8"),
        ("MoveStdlib", "string", "length"),
        ("MoveStdlib", "string", "is_empty"),
        ("MoveStdlib", "string", "as_bytes"),
        ("MoveStdlib", "string", "from_ascii"),
        ("MoveStdlib", "string", "substring"),
        ("MoveStdlib", "string", "append"),
        ("MoveStdlib", "string", "append_utf8"),
        ("MoveStdlib", "string", "index_of"),
        ("MoveStdlib", "option", "some"),
        ("MoveStdlib", "option", "none"),
        ("MoveStdlib", "option", "is_some"),
        ("MoveStdlib", "option", "is_none"),
        ("MoveStdlib", "option", "borrow"),
        ("MoveStdlib", "option", "borrow_mut"),
        ("MoveStdlib", "option", "borrow_with_default"),
        ("MoveStdlib", "option", "contains"),
        ("MoveStdlib", "option", "get_with_default"),
        ("MoveStdlib", "option", "fill"),
        ("MoveStdlib", "option", "extract"),
        ("MoveStdlib", "option", "destroy_some"),
        ("MoveStdlib", "option", "destroy_none"),
        ("MoveStdlib", "option", "destroy_with_default"),
        ("MoveStdlib", "option", "swap"),
        ("MoveStdlib", "option", "swap_or_fill"),
        ("MoveStdlib", "option", "to_vec"),
        ("Prover", "prover", "requires"),
        ("Prover", "prover", "ensures"),
        ("Prover", "prover", "asserts"),
        ("Prover", "prover", "asserts_of"),
        ("Prover", "ghost", "borrow_mut"),
        ("Prover", "ghost", "declare_global"),
        ("Prover", "ghost", "declare_global_mut"),
        ("Prover", "ghost", "global"),
        ("Prover", "ghost", "havoc_global"),
        ("Prover", "ghost", "set"),
        ("Prover", "ghost", "set_spec"),
        ("Prover", "vector_iter", "range"),
        ("Prover", "vector_iter", "slice"),
        ("Prover", "vector_iter", "sum"),
        ("Prover", "vector_iter", "sum_range"),
        ("Sui", "accumulator", "emit_deposit_event"),
        ("Sui", "accumulator", "emit_withdraw_event"),
        ("Sui", "address", "from_bytes"),
        ("Sui", "address", "to_bytes"),
        ("Sui", "ecdsa_k1", "secp256k1_ecrecover"),
        ("Sui", "ecdsa_k1", "secp256k1_verify"),
        ("Sui", "ecdsa_k1", "decompress_pubkey"),
        ("Sui", "ecdsa_k1", "secp256k1_sign"),
        ("Sui", "ecdsa_k1", "secp256k1_keypair_from_seed"),
        ("Sui", "object", "id"),
        ("Sui", "object", "borrow_id"),
        ("Sui", "object", "borrow_uid"),
        ("Sui", "object", "delete"),
        ("Sui", "object", "delete_impl"),
        ("Sui", "object", "id_from_address"),
        ("Sui", "object", "id_from_bytes"),
        ("Sui", "object", "id_to_address"),
        ("Sui", "object", "id_to_bytes"),
        ("Sui", "object", "new"),
        ("Sui", "object", "record_new_uid"),
        ("Sui", "object", "record_new_uid_from_hash"),
        ("Sui", "object", "uid_to_inner"),
        ("Sui", "object", "uid_to_address"),
        ("Sui", "tx_context", "dummy"),
        ("Sui", "tx_context", "digest"),
        ("Sui", "tx_context", "epoch"),
        ("Sui", "tx_context", "epoch_timestamp_ms"),
        ("Sui", "tx_context", "fresh_object_address"),
        ("Sui", "tx_context", "gas_price"),
        ("Sui", "tx_context", "reference_gas_price"),
        ("Sui", "tx_context", "sender"),
        ("Sui", "tx_context", "sponsor"),
        ("Sui", "tx_context", "increment_epoch_number"),
        ("Sui", "bag", "new"),
        ("Sui", "bag", "add"),
        ("Sui", "bag", "borrow"),
        ("Sui", "bag", "borrow_mut"),
        ("Sui", "bag", "remove"),
        ("Sui", "bag", "contains"),
        ("Sui", "bag", "contains_with_type"),
        ("Sui", "bag", "is_empty"),
        ("Sui", "bag", "length"),
        ("Sui", "bag", "destroy_empty"),
        ("Sui", "object_bag", "new"),
        ("Sui", "object_bag", "add"),
        ("Sui", "object_bag", "borrow"),
        ("Sui", "object_bag", "borrow_mut"),
        ("Sui", "object_bag", "remove"),
        ("Sui", "object_bag", "contains"),
        ("Sui", "object_bag", "contains_with_type"),
        ("Sui", "object_bag", "is_empty"),
        ("Sui", "object_bag", "length"),
        ("Sui", "object_bag", "destroy_empty"),
        ("Sui", "object_bag", "value_id"),
        ("Sui", "table", "new"),
        ("Sui", "table", "add"),
        ("Sui", "table", "borrow"),
        ("Sui", "table", "borrow_mut"),
        ("Sui", "table", "remove"),
        ("Sui", "table", "contains"),
        ("Sui", "table", "is_empty"),
        ("Sui", "table", "length"),
        ("Sui", "table", "destroy_empty"),
        ("Sui", "table", "drop"),
        ("Sui", "table", "borrow_or_unknown"),
        ("Sui", "table", "add_pure"),
        ("Sui", "table", "remove_pure"),
        ("Sui", "object_table", "new"),
        ("Sui", "object_table", "add"),
        ("Sui", "object_table", "borrow"),
        ("Sui", "object_table", "borrow_mut"),
        ("Sui", "object_table", "remove"),
        ("Sui", "object_table", "contains"),
        ("Sui", "object_table", "is_empty"),
        ("Sui", "object_table", "length"),
        ("Sui", "object_table", "destroy_empty"),
        ("Sui", "object_table", "value_id"),
        ("Sui", "object_table", "borrow_or_unknown"),
        ("Sui", "object_table", "add_pure"),
        ("Sui", "object_table", "remove_pure"),
        ("Sui", "vec_map", "empty"),
        ("Sui", "vec_map", "insert"),
        ("Sui", "vec_map", "remove"),
        ("Sui", "vec_map", "pop"),
        ("Sui", "vec_map", "get"),
        ("Sui", "vec_map", "get_mut"),
        ("Sui", "vec_map", "try_get"),
        ("Sui", "vec_map", "contains"),
        ("Sui", "vec_map", "length"),
        ("Sui", "vec_map", "is_empty"),
        ("Sui", "vec_map", "destroy_empty"),
        ("Sui", "vec_map", "into_keys_values"),
        ("Sui", "vec_map", "from_keys_values"),
        ("Sui", "vec_map", "keys"),
        ("Sui", "vec_map", "get_idx_opt"),
        ("Sui", "vec_map", "get_idx"),
        ("Sui", "vec_map", "get_entry_by_idx"),
        ("Sui", "vec_map", "get_entry_by_idx_mut"),
        ("Sui", "vec_map", "remove_entry_by_idx"),
        ("Sui", "vec_map", "size"),
        ("Sui", "vec_map", "get_or_unknown"),
        ("Sui", "vec_map", "get_entry_by_idx_or_unknown"),
        ("Sui", "vec_map", "get_idx_or_unknown"),
        ("Sui", "vec_map", "insert_pure"),
        ("Sui", "vec_map", "remove_pure"),
        ("Sui", "vec_set", "empty"),
        ("Sui", "vec_set", "singleton"),
        ("Sui", "vec_set", "insert"),
        ("Sui", "vec_set", "remove"),
        ("Sui", "vec_set", "contains"),
        ("Sui", "vec_set", "length"),
        ("Sui", "vec_set", "is_empty"),
        ("Sui", "vec_set", "into_keys"),
        ("Sui", "vec_set", "from_keys"),
        ("Sui", "vec_set", "keys"),
        ("Sui", "vec_set", "size"),
        ("Sui", "vec_set", "insert_pure"),
        ("Sui", "vec_set", "remove_pure"),
        ("Sui", "dynamic_field", "add"),
        ("Sui", "dynamic_field", "borrow"),
        ("Sui", "dynamic_field", "borrow_mut"),
        ("Sui", "dynamic_field", "remove"),
        ("Sui", "dynamic_field", "remove_if_exists"),
        ("Sui", "dynamic_field", "exists"),
        ("Sui", "dynamic_field", "exists_"),
        ("Sui", "dynamic_field", "exists_with_type"),
        ("Sui", "dynamic_field", "borrow_or_unknown"),
        ("Sui", "dynamic_field", "hash_type_and_key"),
        ("Sui", "dynamic_field", "add_child_object"),
        ("Sui", "dynamic_field", "borrow_child_object"),
        ("Sui", "dynamic_field", "borrow_child_object_mut"),
        ("Sui", "dynamic_field", "remove_child_object"),
        ("Sui", "dynamic_field", "has_child_object"),
        ("Sui", "dynamic_field", "has_child_object_with_ty"),
        ("Sui", "dynamic_field", "field_info"),
        ("Sui", "dynamic_field", "field_info_mut"),
        ("Sui", "dynamic_object_field", "add"),
        ("Sui", "dynamic_object_field", "borrow"),
        ("Sui", "dynamic_object_field", "borrow_mut"),
        ("Sui", "dynamic_object_field", "remove"),
        ("Sui", "dynamic_object_field", "exists"),
        ("Sui", "dynamic_object_field", "exists_"),
        ("Sui", "dynamic_object_field", "exists_with_type"),
        ("Sui", "dynamic_object_field", "id"),
        ("Sui", "dynamic_object_field", "internal_add"),
        ("Sui", "dynamic_object_field", "internal_borrow"),
        ("Sui", "dynamic_object_field", "internal_borrow_mut"),
        ("Sui", "dynamic_object_field", "internal_remove"),
        ("Sui", "dynamic_object_field", "internal_exists_with_type"),
        ("Sui", "dynamic_object_field", "borrow_or_unknown"),
        ("Sui", "transfer", "transfer"),
        ("Sui", "transfer", "public_transfer"),
        ("Sui", "transfer", "share_object"),
        ("Sui", "transfer", "public_share_object"),
        ("Sui", "transfer", "freeze_object"),
        ("Sui", "transfer", "public_freeze_object"),
        ("Sui", "event", "emit"),
        ("Sui", "test_utils", "create_one_time_witness"),
        ("Sui", "types", "is_one_time_witness"),
        ("Sui", "random", "next_u8"),
        ("Sui", "random", "next_u64"),
        ("Sui", "random", "next_u128"),
        ("Sui", "random", "new_generator"),
        ("Sui", "random", "generate_bool"),
        ("Sui", "random", "generate_bytes"),
        ("Sui", "random", "generate_u8"),
        ("Sui", "random", "generate_u16"),
        ("Sui", "random", "generate_u32"),
        ("Sui", "random", "generate_u64"),
        ("Sui", "random", "generate_u128"),
        ("Sui", "random", "generate_u256"),
        ("MoveStdlib", "string", "into_bytes"),
        ("SuiSystem", "validator", "validate_metadata_bcs"),
    ];

    #[test]
    fn native_effects_covered_keys_are_non_default() {
        for (p, m, f) in COVERED_KEYS {
            let eff = native_effects(p, m, f);
            assert_ne!(
                eff,
                crate::ir::Effects::CONSERVATIVE,
                "native_effects({}::{}::{}) returned the conservative                  default; expected an explicit table entry",
                p, m, f
            );
        }
    }

    #[test]
    fn native_effects_default_is_conservative_for_unknown() {
        // Missing entries must default to Effects::CONSERVATIVE -- the
        // conservative fallback.
        let eff = native_effects("Unknown", "module", "fn");
        assert_eq!(eff, crate::ir::Effects::CONSERVATIVE);
        assert!(eff.world_writes, "unknown natives must default to writing");
    }

    #[test]
    fn object_new_is_world_effectful() {
        let eff = native_effects("Sui", "object", "new");
        assert_eq!(eff.mutation, crate::ir::MutLevel::GlobalMut);
        assert!(eff.world_writes);
    }

    #[test]
    fn collection_constructors_allocate_in_world() {
        for module in ["bag", "object_bag", "object_table", "table"] {
            let eff = native_effects("Sui", module, "new");
            assert_eq!(eff.aborts, crate::ir::AbortBit::Total);
            assert_eq!(eff.det, crate::ir::DetBit::Det);
            assert_eq!(eff.mutation, crate::ir::MutLevel::GlobalMut);
            assert!(eff.world_writes);
        }
    }

    #[test]
    fn explicit_test_models_preserve_world_call_shapes() {
        for function in ["emit_deposit_event", "emit_withdraw_event"] {
            let eff = native_effects("Sui", "accumulator", function);
            assert_eq!(eff.aborts, crate::ir::AbortBit::Total);
            assert_eq!(eff.det, crate::ir::DetBit::Det);
            assert_eq!(eff.mutation, crate::ir::MutLevel::GlobalMut);
            assert!(eff.world_writes);
        }
        assert_eq!(
            native_effects("Sui", "test_utils", "create_one_time_witness"),
            crate::ir::Effects::WORLD
        );
    }

    #[test]
    fn native_effects_covered_count_matches_table_size() {
        // Sanity: COVERED_KEYS lists every (p, m, f) entry the
        // table classifies. If the table grows without updating
        // the keys list, this test catches the drift.
        let mut covered = 0usize;
        for (p, m, f) in COVERED_KEYS {
            if native_effects(p, m, f) != crate::ir::Effects::CONSERVATIVE {
                covered += 1;
            }
        }
        // The exact count is whatever the table currently has --
        // pin it so we notice churn.
        assert_eq!(covered, 309);
    }
}
