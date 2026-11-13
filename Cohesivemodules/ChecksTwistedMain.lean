import Cohesivemodules.MainTwisted

set_option linter.style.header false

/-!
# Checks for Z3.v: axioms of the twisted main theorem

Blueprint item Z3.v (`blueprint/blueprint-tw.md` §2.4; definition of done in `CLAUDE.md`):
`#print axioms Cohesive.main_theorem_twisted` lists only `propext`, `Classical.choice` and
`Quot.sound`. `#guard_msgs` makes this a check: the build fails if the printed list ever differs
from the expected message in the docstring above it.
-/

/-- info: 'Cohesive.main_theorem_twisted' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.main_theorem_twisted
