open Lean Meta

private structure Z3Attestation where
  used : Bool := false
  valid : Bool := true
  deriving Inhabited

private def Z3Attestation.merge
    (left right : Z3Attestation) : Z3Attestation :=
  { used := left.used || right.used
    valid := left.valid && right.valid }

private def invalidZ3Attestation : Z3Attestation :=
  { valid := false }

-- `seen` is the declaration traversal memo, keyed by `(name, context)`.
-- `oracleReach` caches the `collectAxioms` verdict per constant: the
-- environment is fixed for the whole query, so a name's axiom closure -- and
-- therefore whether it reaches the oracle -- cannot change between visits.
-- Without it every constant occurrence in a proof term repays a full
-- transitive closure walk, which dominates the audit on real corpora.
private structure Z3AttestationState where
  seen : NameSet := {}
  oracleReach : NameMap Bool := {}

private def reachesZ3Oracle (oracle name : Name) :
    StateT Z3AttestationState MetaM Bool := do
  if let some cached := (← get).oracleReach.find? name then
    return cached
  let axioms ← Lean.collectAxioms name
  let reaches := axioms.contains oracle
  modify fun state =>
    { state with oracleReach := state.oracleReach.insert name reaches }
  return reaches

-- `getUsedConstants` reports exactly the constant occurrences `inspectZ3Expr`
-- reaches: both descend into `.app`, `.lam`, `.forallE`, `.letE`, `.mdata` and
-- `.proj` children and stop everywhere else. So when no reported constant is a
-- marker and none reaches the oracle, no marker branch can fire and every
-- `.const` yields the neutral attestation, whose merges are again neutral --
-- the walk returns `{}` and records nothing.
private def isZ3Inert
    (queryMarker explicitMarker oracle : Name) (expressions : Array Expr) :
    StateT Z3AttestationState MetaM Bool := do
  for expression in expressions do
    for name in expression.getUsedConstants do
      if name == queryMarker || name == explicitMarker || name == oracle then
        return false
      if ← reachesZ3Oracle oracle name then
        return false
  return true

mutual
  private partial def inspectZ3Expr
      (queryMarker explicitMarker oracle : Name) (expression : Expr)
      (context : Nat) : StateT Z3AttestationState MetaM Z3Attestation := do
    let function := expression.getAppFn
    let arguments := expression.getAppArgs
    if function.isConstOf explicitMarker then
      if context != 0 || arguments.size != 2 then
        return invalidZ3Attestation
      let typeResult ← inspectZ3Expr queryMarker explicitMarker oracle arguments[0]! 0
      let proofResult ← inspectZ3Expr queryMarker explicitMarker oracle arguments[1]! 1
      return {
        used := proofResult.used
        valid := typeResult.valid && !typeResult.used &&
          proofResult.valid && proofResult.used
      }
    if function.isConstOf queryMarker then
      if context != 1 || arguments.size != 2 then
        return invalidZ3Attestation
      let typeResult ← inspectZ3Expr queryMarker explicitMarker oracle arguments[0]! 0
      let proofResult ← inspectZ3Expr queryMarker explicitMarker oracle arguments[1]! 2
      return {
        used := proofResult.used
        valid := typeResult.valid && !typeResult.used &&
          proofResult.valid && proofResult.used
      }
    if function.isConstOf oracle then
      if context != 2 || arguments.size != 1 then
        return invalidZ3Attestation
      let typeResult ← inspectZ3Expr queryMarker explicitMarker oracle arguments[0]! 0
      return {
        used := true
        valid := typeResult.valid && !typeResult.used
      }
    match expression with
    | .const name _ =>
      if ← reachesZ3Oracle oracle name then
        inspectZ3Decl queryMarker explicitMarker oracle name 0
      else
        return {}
    | .app fn argument =>
      return (← inspectZ3Expr queryMarker explicitMarker oracle fn context).merge
        (← inspectZ3Expr queryMarker explicitMarker oracle argument context)
    | .lam _ domain body _ | .forallE _ domain body _ =>
      return (← inspectZ3Expr queryMarker explicitMarker oracle domain context).merge
        (← inspectZ3Expr queryMarker explicitMarker oracle body context)
    | .letE _ type value body _ =>
      return ((← inspectZ3Expr queryMarker explicitMarker oracle type context).merge
        (← inspectZ3Expr queryMarker explicitMarker oracle value context)).merge
        (← inspectZ3Expr queryMarker explicitMarker oracle body context)
    | .mdata _ body | .proj _ _ body =>
      inspectZ3Expr queryMarker explicitMarker oracle body context
    | _ => return {}

  private partial def inspectZ3Decl
      (queryMarker explicitMarker oracle name : Name) (context : Nat) :
      StateT Z3AttestationState MetaM Z3Attestation := do
    let key := Name.mkNum name context
    if (← get).seen.contains key then return {}
    modify fun state => { state with seen := state.seen.insert key }
    let env ← getEnv
    let some info := env.find? name | return invalidZ3Attestation
    if info.isUnsafe then return invalidZ3Attestation
    let some value := info.value? true
      | return (← inspectZ3Expr queryMarker explicitMarker oracle info.type 0).merge
          invalidZ3Attestation
    if ← isZ3Inert queryMarker explicitMarker oracle #[info.type, value] then
      return {}
    let typeResult ← inspectZ3Expr queryMarker explicitMarker oracle info.type 0
    return typeResult.merge
      (← inspectZ3Expr queryMarker explicitMarker oracle value context)
end
