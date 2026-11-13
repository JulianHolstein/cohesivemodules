import Cohesivemodules.Comparison.TwistedFullyFaithfulDolbeault

set_option linter.style.header false

/-!
# Checks for Z3.s (C4^tw): axioms

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F, §5): `#print axioms` of the generic
full faithfulness of `J_T` and of its Dolbeault instance (only the standard three).
-/

/-- info: 'Cohesive.bijective_twistedJ_map' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.bijective_twistedJ_map

/-- info: 'Cohesive.full_twistedJ_dolbeault' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.full_twistedJ_dolbeault

/-- info: 'Cohesive.faithful_twistedJ_dolbeault' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.faithful_twistedJ_dolbeault
