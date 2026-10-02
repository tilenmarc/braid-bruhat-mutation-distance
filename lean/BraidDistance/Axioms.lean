import BraidDistance.Main

/-!
# Axiom audit

Prints the axioms on which Theorem 5.4 (`main_theorem`) and its corollaries depend.  The expected output
consists only of Lean's standard axioms (`propext`, `Quot.sound`, possibly `Classical.choice`); in particular
no `sorryAx` and no `Lean.ofReduceBool` (which `native_decide` would introduce).
-/

#print axioms BraidDistance.main_theorem
#print axioms BraidDistance.braid_distance_eq
#print axioms BraidDistance.exists_min_cover
