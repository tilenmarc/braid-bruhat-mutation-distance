import BraidDistance.BasicLemmas

/-!
# Four elements: the packet cycle and arc orders (Section 2.4, Lemma 2.10)

The packet of a 4-set `a < b < c < d` lists the values on `abc, abd, acd, bcd` (coordinates `0, 1, 2, 3`).

* Lemma 2.10: exactly eight sign sequences of length 4 have at most one sign change, `v₀, …, v₇`, and they
  form a cycle in which `v_i, v_{i+1}` differ in coordinate `3 - (i mod 4)` (0-based).
* Along a flip walk, the packet of `abcd` changes exactly at the flips of the four triples of `abcd`, by flipping
  the corresponding coordinate (`packet_flipList`), and stays a valid packet (`arcSeq_of_flipWalk`).
* Arc orders of length 3 are unique (`arc3_unique`): if the packet goes from `x` to `y` (Hamming distance 3) by
  flipping three distinct coordinates, staying valid, then the order of the coordinates is determined by
  `x` and `y`.  This is a finite check (`decide`).
-/

namespace BraidDistance

/-- Negate the `i`-th entry of a sign list. -/
def flipCoord (x : List Bool) (i : Nat) : List Bool := x.mapIdx fun j b => if j = i then !b else b

/-- The coordinate of a triple in the packet of `abcd`, if it is one of its four triples. -/
def coord4 (a b c d : Nat) (t : Triple) : Option Nat :=
  if t = (a, b, c) then some 0 else if t = (a, b, d) then some 1 else
  if t = (a, c, d) then some 2 else if t = (b, c, d) then some 3 else none

/-- The triple of `abcd` with a given coordinate. -/
def tri4 (a b c d : Nat) : Nat → Triple
  | 0 => (a, b, c)
  | 1 => (a, b, d)
  | 2 => (a, c, d)
  | _ => (b, c, d)

/-- The coordinates flipped by `ts` inside the packet of `abcd`, in order. -/
def pcoords (a b c d : Nat) (ts : List Triple) : List Nat := ts.filterMap (coord4 a b c d)

/-- Flipping the coordinates `cs` one after the other keeps the packet valid at every stage. -/
def ArcSeq (x : List Bool) (cs : List Nat) : Prop :=
  ∀ j < cs.length + 1, oneChange ((cs.take j).foldl flipCoord x) = true

instance (x : List Bool) (cs : List Nat) : Decidable (ArcSeq x cs) := by
  unfold ArcSeq; infer_instance

/-- The eight valid packets `v₀, …, v₇` of Section 2.2, in cyclic order. -/
def validPackets : List (List Bool) :=
  [[true, true, true, true], [true, true, true, false], [true, true, false, false],
   [true, false, false, false], [false, false, false, false], [false, false, false, true],
   [false, false, true, true], [false, true, true, true]]

/-- All sign lists of length 4. -/
def allPackets : List (List Bool) :=
  [true, false].flatMap fun a => [true, false].flatMap fun b => [true, false].flatMap fun c =>
    [true, false].map fun d => [a, b, c, d]

/-- All orders of three distinct coordinates. -/
def orders3 : List (List Nat) :=
  (List.range 4).flatMap fun i => (List.range 4).flatMap fun j => (List.range 4).filterMap fun k =>
    if i ≠ j ∧ i ≠ k ∧ j ≠ k then some [i, j, k] else none

/-- Lemma 2.10, first part: the valid packets are exactly `v₀, …, v₇`. -/
theorem validPackets_spec : ∀ x ∈ allPackets, oneChange x = true ↔ x ∈ validPackets := by
  decide

/-- Lemma 2.10, the cycle: `v_i` and `v_{i+1}` differ in coordinate `3 - (i mod 4)`. -/
theorem packet_cycle : ∀ i < 8,
    flipCoord (validPackets.getD i []) (3 - i % 4) = validPackets.getD ((i + 1) % 8) [] := by
  decide

/-- Arc orders of length 3 are unique. -/
theorem arc3_unique : ∀ x ∈ validPackets, ∀ cs ∈ orders3, ∀ cs' ∈ orders3,
    ArcSeq x cs → ArcSeq x cs' → cs.foldl flipCoord x = cs'.foldl flipCoord x → cs = cs' := by
  decide

set_option linter.unusedSimpArgs false in
/-- The packet after one flip. -/
private theorem packet_flipT (u : SMap) (t : Triple) {a b c d : Nat} (hab : a < b) (hbc : b < c)
    (hcd : c < d) :
    packet (flipT u t) a b c d =
      match coord4 a b c d t with
      | some i => flipCoord (packet u a b c d) i
      | none => packet u a b c d := by
  obtain ⟨x, y, z⟩ := t
  have n1 : a ≠ b := by omega
  have n2 : a ≠ c := by omega
  have n3 : a ≠ d := by omega
  have n4 : b ≠ c := by omega
  have n5 : b ≠ d := by omega
  have n6 : c ≠ d := by omega
  unfold coord4
  by_cases h0 : (x, y, z) = (a, b, c)
  · simp only [Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl, rfl⟩ := h0
    simp [packet, flipT, flipCoord, n1, n2, n3, n4, n5, n6, Ne.symm n1, Ne.symm n2, Ne.symm n3,
      Ne.symm n4, Ne.symm n5, Ne.symm n6]
  by_cases h1 : (x, y, z) = (a, b, d)
  · simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    simp [packet, flipT, flipCoord, n1, n2, n3, n4, n5, n6, Ne.symm n1, Ne.symm n2, Ne.symm n3,
      Ne.symm n4, Ne.symm n5, Ne.symm n6]
  by_cases h2 : (x, y, z) = (a, c, d)
  · simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp [packet, flipT, flipCoord, n1, n2, n3, n4, n5, n6, Ne.symm n1, Ne.symm n2, Ne.symm n3,
      Ne.symm n4, Ne.symm n5, Ne.symm n6]
  by_cases h3 : (x, y, z) = (b, c, d)
  · simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    simp [packet, flipT, flipCoord, n1, n2, n3, n4, n5, n6, Ne.symm n1, Ne.symm n2, Ne.symm n3,
      Ne.symm n4, Ne.symm n5, Ne.symm n6]
  simp only [h0, h1, h2, h3, ite_false]
  simp only [packet, flipT]
  have e0 : ¬ (a, b, c) = (x, y, z) := fun h => h0 h.symm
  have e1 : ¬ (a, b, d) = (x, y, z) := fun h => h1 h.symm
  have e2 : ¬ (a, c, d) = (x, y, z) := fun h => h2 h.symm
  have e3 : ¬ (b, c, d) = (x, y, z) := fun h => h3 h.symm
  simp only [e0, e1, e2, e3, ite_false]

/-- Every prefix of a filtered list is the filter of a prefix. -/
private theorem filterMap_take_prefix {α β : Type} (f : α → Option β) (l : List α) (j : Nat)
    (hj : j ≤ (l.filterMap f).length) :
    ∃ i, i ≤ l.length ∧ (l.take i).filterMap f = (l.filterMap f).take j := by
  induction l generalizing j with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons x l ih =>
    cases j with
    | zero => exact ⟨0, by simp, by simp⟩
    | succ j =>
      cases hx : f x with
      | none =>
        have hj' : j + 1 ≤ (l.filterMap f).length := by simpa [List.filterMap_cons, hx] using hj
        obtain ⟨i, hi, he⟩ := ih (j + 1) hj'
        refine ⟨i + 1, by simp; omega, ?_⟩
        simp [hx, he]
      | some y =>
        have hj' : j ≤ (l.filterMap f).length := by simp [hx] at hj; omega
        obtain ⟨i, hi, he⟩ := ih j hj'
        refine ⟨i + 1, by simp; omega, ?_⟩
        simp [hx, he]

/-- The packet after a list of flips. -/
theorem packet_flipList (u : SMap) (ts : List Triple) {a b c d : Nat} (hab : a < b) (hbc : b < c)
    (hcd : c < d) :
    packet (flipList u ts) a b c d = (pcoords a b c d ts).foldl flipCoord (packet u a b c d) := by
  induction ts generalizing u with
  | nil => rfl
  | cons t ts ih =>
    have h1 : flipList u (t :: ts) = flipList (flipT u t) ts := rfl
    rw [h1, ih, packet_flipT u t hab hbc hcd]
    unfold pcoords
    rw [List.filterMap_cons]
    cases coord4 a b c d t <;> rfl

/-- Along a flip walk the packets stay valid. -/
theorem arcSeq_of_flipWalk {m : Nat} {s : SMap} {ts : List Triple} (hw : FlipWalk m s ts)
    {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < m) :
    ArcSeq (packet s a b c d) (pcoords a b c d ts) := by
  intro j hj
  obtain ⟨i, hi, he⟩ := filterMap_take_prefix (coord4 a b c d) ts j (by unfold pcoords at hj; omega)
  have h := packet_flipList s (ts.take i) hab hbc hcd
  unfold pcoords at h
  rw [he] at h
  unfold pcoords
  rw [← h]
  exact hw.2 i hi d hd c hcd b hbc a hab

/-- The packet of a signotope is valid. -/
theorem packet_mem_validPackets {m : Nat} {u : SMap} (hu : IsSignotope m u) {a b c d : Nat}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < m) : packet u a b c d ∈ validPackets := by
  have h := hu d hd c hcd b hbc a hab
  have hm : packet u a b c d ∈ allPackets := by
    simp only [packet]
    cases u a b c <;> cases u a b d <;> cases u a c d <;> cases u b c d <;> decide
  exact (validPackets_spec _ hm).1 h

end BraidDistance
