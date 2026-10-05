import OMDistance.Sorting

/-!
# The set form of (GP)

In Definition 6.1, `χ(σ, x, y)` is the value of `χ` at the ordered tuple `(σ₁, …, σ_{r-2}, x, y)`, which is
`sgn(π) χ(σ ∪ {x, y})` for the sorting permutation `π`.  For increasing `σ` and `x < y` outside `σ`, sorting
`σ ++ [x, y]` takes `n_x + n_y` inversions, where `n_z = #{i : σ_i > z}` (`inversions_append_two`).  In each of
the three products of (GP) the four factors carry the total sign `(-1)^(n_a + n_b + n_c + n_d)`, so the three
products are multiplied by a common sign and (GP) is equivalent to the same condition with `χ` evaluated on sets:

  `χ(σ∪ab)χ(σ∪cd)`, `-χ(σ∪ac)χ(σ∪bd)`, `χ(σ∪ad)χ(σ∪bc)` are not all equal.

This *set form* is `IsChiroSet` below, written with the six values through `gp6`; `isChirotope_iff_set` proves the
equivalence.  All later files work with the set form.
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- (GP) in terms of the six values `ab = χ(σ∪ab), …, cd = χ(σ∪cd)` on sets: the signs `ab·cd`, `-(ac·bd)`,
`ad·bc` are not all equal. -/
def gp6 (ab ac ad bc bd cd : Bool) : Bool :=
  !((smul ab cd == (!smul ac bd)) && ((!smul ac bd) == smul ad bc))

/-- `χ(σ ∪ {x, y})`, with the set written as a sorted list. -/
def setVal (χ : SignMap) (σ : List Nat) (x y : Nat) : Bool := χ (isort (σ ++ [x, y]))

/-- (GP) at `σ` and `a, b, c, d` in set form. -/
def GPSet (χ : SignMap) (σ : List Nat) (a b c d : Nat) : Prop :=
  gp6 (setVal χ σ a b) (setVal χ σ a c) (setVal χ σ a d) (setVal χ σ b c) (setVal χ σ b d)
    (setVal χ σ c d) = true

/-- The set form of Definition 6.1. -/
def IsChiroSet (M r : Nat) (χ : SignMap) : Prop :=
  2 ≤ r ∧ r ≤ M ∧
    ∀ σ, IsRSet M (r - 2) σ → ∀ d < M, ∀ c < d, ∀ b < c, ∀ a < b,
      a ∉ σ → b ∉ σ → c ∉ σ → d ∉ σ → GPSet χ σ a b c d

/-- `gp6` is exactly the condition "not all equal". -/
theorem gp6_eq_true_iff (ab ac ad bc bd cd : Bool) :
    gp6 ab ac ad bc bd cd = true ↔
      ¬ (smul ab cd = (!smul ac bd) ∧ (!smul ac bd) = smul ad bc) := by
  revert ab ac ad bc bd cd; decide

/-- The parity of `n_z = #{i : σ_i > z}`. -/
private def parAbove (σ : List Nat) (z : Nat) : Bool :=
  (σ.filter fun w => decide (z < w)).length % 2 == 1

/-- `χ(σ, x, y)` is `χ(σ ∪ {x, y})` multiplied by the sign `(-1)^(n_x + n_y)`. -/
private theorem chiPair_eq_setVal {σ : List Nat} (hσ : StrictIncr σ) {x y : Nat} (hxy : x < y)
    (χ : SignMap) :
    chiPair χ σ x y = (setVal χ σ x y ^^ (parAbove σ x ^^ parAbove σ y)) := by
  unfold chiPair tupleVal setVal parAbove
  rw [inversions_append_two hσ hxy]
  generalize (σ.filter fun w => decide (x < w)).length = m
  generalize (σ.filter fun w => decide (y < w)).length = n
  generalize χ (isort (σ ++ [x, y])) = v
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [hm, hn, Nat.add_mod] <;> cases v <;> rfl

/-- The common sign of the three products of (GP) cancels. -/
private theorem gp_bool (ab ac ad bc bd cd pa pb pc pd : Bool) :
    (¬ (smul (ab ^^ (pa ^^ pb)) (cd ^^ (pc ^^ pd)) = (!smul (ac ^^ (pa ^^ pc)) (bd ^^ (pb ^^ pd))) ∧
      (!smul (ac ^^ (pa ^^ pc)) (bd ^^ (pb ^^ pd))) = smul (ad ^^ (pa ^^ pd)) (bc ^^ (pb ^^ pc)))) ↔
      gp6 ab ac ad bc bd cd = true := by
  revert ab ac ad bc bd cd pa pb pc pd; decide

/- The hypotheses `a, b, c, d ∉ σ` are part of the statement but not needed by the proof. -/
set_option linter.unusedVariables false in
/-- (GP) at a single `σ, a, b, c, d` is equivalent to its set form. -/
theorem gp_iff_gpSet {σ : List Nat} (hσ : StrictIncr σ) {a b c d : Nat} (hab : a < b) (hbc : b < c)
    (hcd : c < d) (ha : a ∉ σ) (hb : b ∉ σ) (hc : c ∉ σ) (hd : d ∉ σ) (χ : SignMap) :
    GP χ σ a b c d ↔ GPSet χ σ a b c d := by
  unfold GP GPSet
  rw [chiPair_eq_setVal hσ hab, chiPair_eq_setVal hσ (Nat.lt_trans hab hbc),
    chiPair_eq_setVal hσ (Nat.lt_trans hab (Nat.lt_trans hbc hcd)), chiPair_eq_setVal hσ hbc,
    chiPair_eq_setVal hσ (Nat.lt_trans hbc hcd), chiPair_eq_setVal hσ hcd]
  exact gp_bool _ _ _ _ _ _ _ _ _ _

/-- Definition 6.1 is equivalent to its set form. -/
theorem isChirotope_iff_set {M r : Nat} {χ : SignMap} : IsChirotope M r χ ↔ IsChiroSet M r χ := by
  unfold IsChirotope IsChiroSet
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun σ hσ d hd c hcd b hbc a hab ha hb hc hdσ => ?_⟩
    exact (gp_iff_gpSet hσ.2.1 hab hbc hcd ha hb hc hdσ χ).1 (h3 σ hσ d hd c hcd b hbc a hab ha hb hc hdσ)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun σ hσ d hd c hcd b hbc a hab ha hb hc hdσ => ?_⟩
    exact (gp_iff_gpSet hσ.2.1 hab hbc hcd ha hb hc hdσ χ).2 (h3 σ hσ d hd c hcd b hbc a hab ha hb hc hdσ)

end OMDistance
