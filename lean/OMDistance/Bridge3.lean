import OMDistance.WalkLemmas
import OMDistance.Signotope
import BraidDistance.HammingParity

/-!
# Rank three: the bridge to Part I

Part I works with sign maps on triples (`BraidDistance.SMap`), signotopes `IsSignotope m u`, walks
`Walk m u v k` in `B(m,2)` and the Hamming distance `hamming m u v`.  Via `ofSMap` these are the rank-3 cases of
`IsSignotopeR m 3`, `SigWalk m 3` and `hamR m 3`.  The packets agree: for `P = [a, b, c, d]`,
`rpacket (ofSMap u) P = packet u a b c d`.
-/

namespace OMDistance

private theorem isRSet3 {M : Nat} {X : List Nat} :
    IsRSet M 3 X ↔ ∃ a b c, X = [a, b, c] ∧ a < b ∧ b < c ∧ c < M := by
  constructor
  · rintro ⟨hl, hs, hm⟩
    match X, hl with
    | [a, b, c], _ =>
      simp [BraidDistance.StrictIncr] at hs hm
      exact ⟨a, b, c, rfl, by omega, by omega, by omega⟩
  · rintro ⟨a, b, c, rfl, h1, h2, h3⟩
    refine ⟨rfl, ?_, ?_⟩
    · simp [BraidDistance.StrictIncr]; omega
    · simp; omega

private theorem isRSet4 {M : Nat} {X : List Nat} :
    IsRSet M 4 X ↔ ∃ a b c d, X = [a, b, c, d] ∧ a < b ∧ b < c ∧ c < d ∧ d < M := by
  constructor
  · rintro ⟨hl, hs, hm⟩
    match X, hl with
    | [a, b, c, d], _ =>
      simp [BraidDistance.StrictIncr] at hs hm
      exact ⟨a, b, c, d, rfl, by omega, by omega, by omega, by omega⟩
  · rintro ⟨a, b, c, d, rfl, h1, h2, h3, h4⟩
    refine ⟨rfl, ?_, ?_⟩
    · simp [BraidDistance.StrictIncr]; omega
    · simp; omega

private theorem rpacket4 (χ : SignMap) (a b c d : Nat) :
    rpacket χ [a, b, c, d] = BraidDistance.packet (toSMap χ) a b c d := rfl

private theorem toSMap_ofSMap (u : BraidDistance.SMap) : toSMap (ofSMap u) = u := rfl

private theorem isSignotopeR_iff_toSMap {M : Nat} {χ : SignMap} :
    IsSignotopeR M 3 χ ↔ BraidDistance.IsSignotope M (toSMap χ) := by
  constructor
  · intro h d hd c hc b hb a ha
    rw [← rpacket4]
    exact h _ (isRSet4.2 ⟨a, b, c, d, rfl, ha, hb, hc, hd⟩)
  · intro h P hP
    obtain ⟨a, b, c, d, rfl, h1, h2, h3, h4⟩ := isRSet4.1 hP
    rw [rpacket4]
    exact h d h4 c h3 b h2 a h1

private theorem agreeR_iff_toSMap {M : Nat} {χ ψ : SignMap} :
    AgreeR M 3 χ ψ ↔ BraidDistance.Agree M (toSMap χ) (toSMap ψ) := by
  constructor
  · intro h a b c h1 h2 h3
    exact h _ (isRSet3.2 ⟨a, b, c, rfl, h1, h2, h3⟩)
  · intro h X hX
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := isRSet3.1 hX
    exact h a b c h1 h2 h3

private theorem differsInOneR_iff_toSMap {M : Nat} {χ ψ : SignMap} :
    DiffersInOneR M 3 χ ψ ↔ BraidDistance.DiffersInOne M (toSMap χ) (toSMap ψ) := by
  constructor
  · rintro ⟨X, hX, hne, hrest⟩
    obtain ⟨a, b, c, rfl, h1, h2, h3⟩ := isRSet3.1 hX
    refine ⟨(a, b, c), ⟨h1, h2, h3⟩, hne, ?_⟩
    rintro ⟨a', b', c'⟩ ⟨h1', h2', h3'⟩ hne'
    apply hrest _ (isRSet3.2 ⟨a', b', c', rfl, h1', h2', h3'⟩)
    intro heq
    simp at heq
    apply hne'
    simp [heq]
  · rintro ⟨⟨a, b, c⟩, ⟨h1, h2, h3⟩, hne, hrest⟩
    refine ⟨[a, b, c], isRSet3.2 ⟨a, b, c, rfl, h1, h2, h3⟩, hne, ?_⟩
    intro Y hY hYX
    obtain ⟨a', b', c', rfl, h1', h2', h3'⟩ := isRSet3.1 hY
    apply hrest (a', b', c') ⟨h1', h2', h3'⟩
    intro heq
    simp at heq
    apply hYX
    simp [heq]

private theorem flatMap_singleton_eq_map {α β : Type} (g : α → β) (l : List α) :
    l.flatMap (fun x => [g x]) = l.map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem rsets_three (M : Nat) :
    rsets M 3 = (BraidDistance.triples M).map fun t => [t.1, t.2.1, t.2.2] := by
  simp only [rsets, rsetsFrom, BraidDistance.triples, List.map_flatMap, List.range_eq_range', List.map_map,
    List.map_cons, List.map_nil]
  simp only [flatMap_singleton_eq_map]
  rfl

private theorem hamR_toSMap (M : Nat) (χ ψ : SignMap) :
    hamR M 3 χ ψ = BraidDistance.hamming M (toSMap χ) (toSMap ψ) := by
  unfold hamR diffR BraidDistance.hamming BraidDistance.diffList
  rw [rsets_three, List.filter_map, List.length_map]
  rfl

private theorem sigWalk_toSMap {M : Nat} {χ ψ : SignMap} {k : Nat} (hw : SigWalk M 3 χ ψ k) :
    BraidDistance.Walk M (toSMap χ) (toSMap ψ) k := by
  induction hw with
  | nil hs ha => exact .nil (isSignotopeR_iff_toSMap.1 hs) (agreeR_iff_toSMap.1 ha)
  | cons hs hd _ ih => exact .cons (isSignotopeR_iff_toSMap.1 hs) (differsInOneR_iff_toSMap.1 hd) ih

theorem ofSMap_toSMap (M : Nat) (χ : SignMap) : AgreeR M 3 (ofSMap (toSMap χ)) χ := by
  intro X hX
  obtain ⟨a, b, c, rfl, -⟩ := isRSet3.1 hX
  rfl

theorem isSignotopeR_ofSMap {M : Nat} {u : BraidDistance.SMap} :
    IsSignotopeR M 3 (ofSMap u) ↔ BraidDistance.IsSignotope M u :=
  isSignotopeR_iff_toSMap

theorem hamR_ofSMap (M : Nat) (u v : BraidDistance.SMap) :
    hamR M 3 (ofSMap u) (ofSMap v) = BraidDistance.hamming M u v :=
  hamR_toSMap M _ _

/-- A walk in `B(m,2)` in the sense of Part I is a walk of rank-3 signotopes. -/
theorem walk_to_sigWalk {M : Nat} {u v : BraidDistance.SMap} {k : Nat} (hw : BraidDistance.Walk M u v k) :
    SigWalk M 3 (ofSMap u) (ofSMap v) k := by
  induction hw with
  | nil hs ha => exact .nil (isSignotopeR_iff_toSMap.2 hs) (agreeR_iff_toSMap.2 ha)
  | @cons u' v' _ _ hs hd _ ih =>
    exact .cons (isSignotopeR_iff_toSMap.2 hs) (differsInOneR_iff_toSMap (ψ := ofSMap v').2 hd) ih

/-- A walk of rank-3 signotopes is a walk in `B(m,2)` in the sense of Part I. -/
theorem sigWalk_to_walk {M : Nat} {u v : BraidDistance.SMap} {k : Nat} (hw : SigWalk M 3 (ofSMap u) (ofSMap v) k) :
    BraidDistance.Walk M u v k :=
  sigWalk_toSMap hw

end OMDistance
