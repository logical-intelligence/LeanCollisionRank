import CollisionRank.Main
import Lean.Util.CollectAxioms

set_option autoImplicit false

/-! Fail on an undeclared axiom or any sorry dependency in ANY declaration
from an implementation module, including unused helpers and private constants.
The guarded reports below additionally fix the exact dependencies of the
seven main theorems and four structural checks. -/
open Lean in
run_cmd do
  let env ← getEnv
  let externalAxioms : Array Name := #[
    `CollisionRank.SturmianGroup,
    `CollisionRank.sturmianGroupStructure,
    `CollisionRank.sturmianRealization,
    `CollisionRank.sturmianHalfLineLocalFinite,
    `CollisionRank.sturmianScaledPeriodicWindow,
    `CollisionRank.InSG,
    `CollisionRank.sturmian_not_in_SG]
  let allowed := externalAxioms ++ #[`propext, `Quot.sound, `Classical.choice]
  let mut checked : Nat := 0
  let mut seenAxioms : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    unless (`CollisionRank).isPrefixOf moduleName do
      continue
    checked := checked + 1
    match info with
    | .axiomInfo _ =>
      unless externalAxioms.contains name do
        throwError "Undeclared project axiom: {name}"
      seenAxioms := seenAxioms.push name
    | _ => pure ()
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "Forbidden axiom {ax} in declaration {name}"
  for ax in externalAxioms do
    unless seenAxioms.contains ax do
      throwError "Expected project axiom is absent: {ax}"
  logInfo m!"GLOBAL_AXIOM_AUDIT_PASS: {checked} implementation declarations; exactly {seenAxioms.size} project axioms; no sorryAx dependencies."

/-- info: 'CollisionRank.certificateCollisionSet_isLabelSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.certificateCollisionSet_isLabelSet

/-- info: 'CollisionRank.abstractCore_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.abstractCore_symmetric

/-- info: 'CollisionRank.periodicSeparationCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.periodicSeparationCertificate

/-- info: 'CollisionRank.relative_symmetric_rank_at_most_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.relative_symmetric_rank_at_most_two

/-- info: 'CollisionRank.relative_symmetric_rank_at_most_two_expanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.relative_symmetric_rank_at_most_two_expanded

/-- info: 'CollisionRank.sturmian_symmetric_rank_at_most_two' depends on axioms: [propext,
 Classical.choice,
 CollisionRank.SturmianGroup,
 CollisionRank.sturmianGroupStructure,
 CollisionRank.sturmianHalfLineLocalFinite,
 CollisionRank.sturmianRealization,
 CollisionRank.sturmianScaledPeriodicWindow,
 Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.sturmian_symmetric_rank_at_most_two

/-- info: 'CollisionRank.exists_group_symmetric_rank_at_most_two_given_assumed_non_SG' depends on axioms: [propext,
 Classical.choice,
 CollisionRank.InSG,
 CollisionRank.SturmianGroup,
 CollisionRank.sturmianGroupStructure,
 CollisionRank.sturmianHalfLineLocalFinite,
 CollisionRank.sturmianRealization,
 CollisionRank.sturmianScaledPeriodicWindow,
 CollisionRank.sturmian_not_in_SG,
 Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.exists_group_symmetric_rank_at_most_two_given_assumed_non_SG

/-- info: 'CollisionRank.fixedStageAt_iff_finiteFixedStageAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.fixedStageAt_iff_finiteFixedStageAt

/-- info: 'CollisionRank.fixedReducesIn_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.fixedReducesIn_padding

/-- info: 'CollisionRank.symmetricReducesIn_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.symmetricReducesIn_padding

/-- info: 'CollisionRank.periodFour_symmetric_smoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CollisionRank.periodFour_symmetric_smoke
