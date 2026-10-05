import OMDistance.SigChiro

/-!
# The positive fibre (Proposition 6.9)

Let `r ≥ 2`, `S = [M]` with `M ≥ r`, and `Ω = [M+1]` with `∞ = M`.  Then `Pos_r(u) = posF M u` is a uniform
chirotope of rank `r` on `Ω` if and only if `u` is a signotope of rank `r` on `S`.

* (⇐) `posF M u` is itself a signotope (`posF_signotope`: the packets of `(r+1)`-subsets of `S` are those of `u`,
  and the packet of `Q ∪ {∞}` is `(u(Q), +, …, +)`), hence a chirotope by `signotope_isChirotope`.
* (⇒) (GP) of `posF M u` at `σ` and `x < y < z < ∞` says, in set form, that
  `(u(σ∪xy), -u(σ∪xz), u(σ∪yz))` are not all equal, i.e. that `(u(σ∪xy), u(σ∪xz), u(σ∪yz))` has at most one sign
  change; by `signotope_of_triples`, `u` is a signotope.
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- (GP) at `(σ; x, y, z, ∞)` for the positive fibre, where the three values involving `∞` are `+`, says that
`(ab, ac, bc)` has at most one sign change. -/
private theorem gp6_fibre (ab ac bc : Bool) (h : gp6 ab ac true bc true true = true) :
    BraidDistance.oneChange [ab, ac, bc] = true := by
  revert ab ac bc h; decide

/-- A list of `+` signs preceded by `+` has no sign change. -/
private theorem signChanges_true_all : ∀ l : List Bool, (∀ b ∈ l, b = true) →
    BraidDistance.signChanges (true :: l) = 0
  | [], _ => rfl
  | b :: l, h => by
    have hb : b = true := h b (List.mem_cons_self ..)
    subst hb
    have := signChanges_true_all l (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp [BraidDistance.signChanges, this]

/-- A list `(a, +, …, +)` has at most one sign change. -/
private theorem oneChange_head (a : Bool) (l : List Bool) (h : ∀ b ∈ l, b = true) :
    BraidDistance.oneChange (a :: l) = true := by
  unfold BraidDistance.oneChange
  cases l with
  | nil => simp [BraidDistance.signChanges]
  | cons b l =>
    have hb : b = true := h b (List.mem_cons_self ..)
    subst hb
    have := signChanges_true_all l (fun c hc => h c (List.mem_cons_of_mem _ hc))
    apply decide_eq_true
    show (if a = true then 0 else 1) + BraidDistance.signChanges (true :: l) ≤ 1
    rw [this]
    split <;> omega

/-- `posF M u` is `+` on sets containing `∞ = M`. -/
private theorem posF_of_mem {M : Nat} (u : SignMap) {B : List Nat} (h : M ∈ B) : posF M u B = true := by
  simp [posF, h]

/-- `posF M u` agrees with `u` on sets avoiding `∞ = M`. -/
private theorem posF_of_not_mem {M : Nat} (u : SignMap) {B : List Nat} (h : M ∉ B) : posF M u B = u B := by
  simp [posF, h]

/-- A subset of `[M+1]` containing `M` has `M` as its last element: it is `Q ++ [M]`. -/
private theorem split_last {M n : Nat} {P : List Nat} (hP : IsRSet (M + 1) n P) (hM : M ∈ P) :
    ∃ Q, P = Q ++ [M] := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hM
  refine ⟨A, ?_⟩
  cases B with
  | nil => rfl
  | cons b B =>
    exfalso
    have hinc := hP.2.1
    unfold StrictIncr at hinc
    rw [List.pairwise_append] at hinc
    have h1 : M < b := (List.pairwise_cons.1 hinc.2.1).1 b (List.mem_cons_self ..)
    have h2 : b < M + 1 := hP.2.2 b (by simp)
    omega

/-- The positive fibre of a signotope is a signotope (on `[M+1]`). -/
theorem posF_signotope {M r : Nat} {u : SignMap} (hu : IsSignotopeR M r u) :
    IsSignotopeR (M + 1) r (posF M u) := by
  intro P hP
  by_cases hM : M ∈ P
  · obtain ⟨Q, rfl⟩ := split_last hP hM
    have hlen : Q.length = r := by
      have := hP.1; simp at this; omega
    unfold rpacket
    rw [List.length_append, List.length_singleton, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.map_cons]
    apply oneChange_head
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    rw [List.mem_reverse, List.mem_range] at hi
    apply posF_of_mem
    rw [List.eraseIdx_append_of_lt_length hi]
    simp
  · have hP' : IsRSet M (r + 1) P :=
      ⟨hP.1, hP.2.1, fun x hx => by
        have h1 := hP.2.2 x hx
        have h2 : x ≠ M := fun h => hM (h ▸ hx)
        omega⟩
    have e : rpacket (posF M u) P = rpacket u P := by
      unfold rpacket
      apply List.map_congr_left
      intro i _
      apply posF_of_not_mem
      exact fun h => hM ((List.eraseIdx_sublist P i).subset h)
    rw [e]
    exact hu P hP'

/-- Proposition 6.9 (⇐): the positive fibre of a signotope is a uniform chirotope. -/
theorem fibre_backward {M r : Nat} (hr : 2 ≤ r) (hrM : r ≤ M) {u : SignMap} (hu : IsSignotopeR M r u) :
    IsChirotope (M + 1) r (posF M u) :=
  signotope_isChirotope hr (Nat.le_succ_of_le hrM) (posF_signotope hu)

/-- Proposition 6.9 (⇒): if the positive fibre of `u` is a uniform chirotope, then `u` is a signotope. -/
theorem fibre_forward {M r : Nat} (hr : 2 ≤ r) {u : SignMap} (hχ : IsChirotope (M + 1) r (posF M u)) :
    IsSignotopeR M r u := by
  rw [isChirotope_iff_set] at hχ
  obtain ⟨_, _, h⟩ := hχ
  apply signotope_of_triples hr
  intro σ hσ z hz y hyz x hxy hx hy hzσ
  have hσ' : IsRSet (M + 1) (r - 2) σ := hσ.mono (Nat.le_succ M)
  have hMσ : M ∉ σ := fun hm => Nat.lt_irrefl _ (hσ.2.2 M hm)
  have g := h σ hσ' M (Nat.lt_succ_self M) z hz y hyz x hxy hx hy hzσ hMσ
  unfold GPSet at g
  have e1 : ∀ a b, a < M → b < M → setVal (posF M u) σ a b = setVal u σ a b := by
    intro a b ha hb
    unfold setVal
    apply posF_of_not_mem
    intro hm
    rw [mem_isort, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hMσ hm
    · simp at hm; omega
  have e2 : ∀ a, setVal (posF M u) σ a M = true := by
    intro a
    unfold setVal
    apply posF_of_mem
    rw [mem_isort]
    simp
  have hyM : y < M := Nat.lt_trans hyz hz
  have hxM : x < M := Nat.lt_trans hxy hyM
  rw [e1 x y hxM hyM, e1 x z hxM hz, e1 y z hyM hz, e2, e2, e2] at g
  exact gp6_fibre _ _ _ g

/-- Proposition 6.9. -/
theorem fibre {M r : Nat} (hr : 2 ≤ r) (hrM : r ≤ M) (u : SignMap) :
    IsChirotope (M + 1) r (posF M u) ↔ IsSignotopeR M r u :=
  ⟨fibre_forward hr, fibre_backward hr hrM⟩

end OMDistance
