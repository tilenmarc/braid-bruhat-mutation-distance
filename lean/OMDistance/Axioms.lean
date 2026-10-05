import OMDistance

/-!
# Axiom check for Part II (not part of the default build target)

`lake env lean OMDistance/Axioms.lean` prints the axioms of the main results of Part II.  Every line should read
`[propext, Classical.choice, Quot.sound]` or a subset of it; `sorryAx` in any line marks an unfinished proof.
-/

-- Theorem 7.2 (rank three), `OMDistance/MainRank3.lean`
#print axioms OMDistance.rank3_theorem
#print axioms OMDistance.rank3_distance_eq
#print axioms OMDistance.range_cover
#print axioms OMDistance.sG_signotope
#print axioms OMDistance.vG_signotope

-- Proposition 7.1, `OMDistance/LowerRank3.lean`
#print axioms OMDistance.prop_lower

-- Gadget step of Proposition 7.1, `OMDistance/GadgetChiro.lean`
#print axioms OMDistance.gadget_no_walk30
#print axioms OMDistance.gadget_chiro_no30
#print axioms OMDistance.gadget_chiro_extra

-- Proposition 8.5, `OMDistance/Excess.lean`, `ExcessLower.lean`, `ExcessUpper.lean`
#print axioms OMDistance.prop_excess
#print axioms OMDistance.excess_lower
#print axioms OMDistance.excess_upper

-- Theorem 8.6 and Corollary 8.7, `OMDistance/MainHigher.lean`
#print axioms OMDistance.higher_rank_theorem
#print axioms OMDistance.hbo_reduction
#print axioms OMDistance.chiro_reduction
#print axioms OMDistance.allranks_reduction

-- Proposition 6.9, `OMDistance/Fibre.lean`
#print axioms OMDistance.fibre
#print axioms OMDistance.fibre_forward
#print axioms OMDistance.fibre_backward

-- Lemma 6.10, `OMDistance/Sheet.lean`
#print axioms OMDistance.sheet_a
#print axioms OMDistance.sheet_b

-- Lemma 8.4, `OMDistance/LiftFlip.lean`
#print axioms OMDistance.liftflip
