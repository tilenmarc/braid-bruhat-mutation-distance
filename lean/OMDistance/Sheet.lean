import OMDistance.Fibre
import OMDistance.ChiroBasic

/-!
# Walks and the positive fibre (Lemma 6.10)

* `D(Pos u, Pos v) = D(u, v)` (`diffR_posF`): the bases through `∞` have sign `+` in both.
* `Pos_r(u)^X = Pos_r(u^X)` for `X ⊆ S` (`posF_flipR`).
* (b) `Pos_r` maps walks in `B(S, r-1)` to walks of chirotopes of the same length (`sheet_b`).
* (a) A walk of chirotopes of length `|D(u, v)|` from `Pos_r u` to `Pos_r v` flips only sets of `D(u, v)`
  (Lemma 2.5), none of which contains `∞`; so every term is positive at `∞`, hence the positive fibre of a
  signotope (Proposition 6.9), and the walk comes from a walk in `B(S, r-1)` (`sheet_a`).
-/

namespace OMDistance

/-- `D(Pos u, Pos v) = D(u, v)`, as lists. -/
theorem diffR_posF (M r : Nat) (u v : SignMap) : diffR (M + 1) r (posF M u) (posF M v) = diffR M r u v := by
  unfold diffR
  rw [← rsets_succ_filter M r, List.filter_filter]
  apply List.filter_congr
  intro X _
  by_cases h : M ∈ X
  · simp [posF, h]
  · simp [posF, h]

theorem hamR_posF (M r : Nat) (u v : SignMap) : hamR (M + 1) r (posF M u) (posF M v) = hamR M r u v := by
  unfold hamR; rw [diffR_posF]

/-- `Pos_r(u^X) = Pos_r(u)^X` for an `r`-subset `X` of `S = [M]`. -/
theorem posF_flipR {M r : Nat} (u : SignMap) {X : List Nat} (hX : IsRSet M r X) :
    posF M (flipR u X) = flipR (posF M u) X := by
  funext Y
  by_cases hYX : Y = X
  · subst hYX
    have hM : M ∉ Y := fun h => Nat.lt_irrefl M (hX.2.2 M h)
    simp [posF, flipR, hM]
  · simp [posF, flipR, hYX]

/-- An `r`-subset of `[M+1]` not containing `M` is an `r`-subset of `[M]`. -/
private theorem isRSet_of_not_mem {M r : Nat} {X : List Nat} (hX : IsRSet (M + 1) r X) (hM : M ∉ X) :
    IsRSet M r X := by
  refine ⟨hX.1, hX.2.1, fun x hx => ?_⟩
  have h1 := hX.2.2 x hx
  have h2 : x ≠ M := fun h => hM (h ▸ hx)
  omega

theorem posF_congr {M r : Nat} {u v : SignMap} (h : AgreeR M r u v) : AgreeR (M + 1) r (posF M u) (posF M v) := by
  intro X hX
  by_cases hM : M ∈ X
  · simp [posF, hM]
  · simp only [posF, hM, ite_false]
    exact h X (isRSet_of_not_mem hX hM)

/-- `Pos_r(u^{X₁⋯X_k}) = Pos_r(u)^{X₁⋯X_k}` for `r`-subsets `X_i` of `S = [M]`. -/
private theorem posF_flipsR {M r : Nat} (u : SignMap) {Xs : List (List Nat)} (hXs : ∀ X ∈ Xs, IsRSet M r X) :
    posF M (flipsR u Xs) = flipsR (posF M u) Xs := by
  induction Xs generalizing u with
  | nil => rfl
  | cons X Xs ih =>
    rw [flipsR_cons, flipsR_cons, ← posF_flipR u (hXs X (by simp))]
    exact ih (flipR u X) (fun Y hY => hXs Y (by simp [hY]))

/-- Lemma 6.10(b). -/
theorem sheet_b {M r : Nat} (hr : 2 ≤ r) (hrM : r ≤ M) {u v : SignMap} {k : Nat} (hw : SigWalk M r u v k) :
    ChiroWalk (M + 1) r (posF M u) (posF M v) k := by
  induction hw with
  | nil hu huv => exact RWalk.nil (fibre_backward hr hrM hu) (posF_congr huv)
  | @cons u v w k hu hd _ ih =>
    refine RWalk.cons (fibre_backward hr hrM hu) ?_ ih
    obtain ⟨X, hX, hag⟩ := differsInOneR_iff.1 hd
    refine differsInOneR_iff.2 ⟨X, hX.mono (Nat.le_succ M), ?_⟩
    rw [← posF_flipR u hX]
    exact posF_congr hag

/-- Lemma 6.10(a): a walk of chirotopes of length `|D(u, v)|` from `Pos_r u` to `Pos_r v` comes from a walk in
`B(S, r-1)` of the same length. -/
theorem sheet_a {M r : Nat} (hr : 2 ≤ r) {u v : SignMap}
    (hw : ChiroWalk (M + 1) r (posF M u) (posF M v) (hamR M r u v)) : SigWalk M r u v (hamR M r u v) := by
  obtain ⟨Xs, hlen, ⟨hXs, hpre⟩, hend⟩ := rwalk_to_flips (isChirotope_agreeInv (M + 1) r) hw
  -- every flipped set lies in `D(Pos u, Pos v)`
  have hD : ∀ X ∈ Xs, X ∈ diffR (M + 1) r (posF M u) (posF M v) := by
    have hle := diffR_filter_le hend (fun X => decide (X ∈ diffR (M + 1) r (posF M u) (posF M v)))
    rw [List.filter_eq_self.2 (fun X hX => by simpa using hX)] at hle
    have hlen' : (diffR (M + 1) r (posF M u) (posF M v)).length = Xs.length := by
      rw [hlen, ← hamR_posF M r u v]; rfl
    have hall := List.length_filter_eq_length_iff.1
      (Nat.le_antisymm (List.length_filter_le _ _) (hlen' ▸ hle))
    intro X hX
    simpa using hall X hX
  have hXsM : ∀ X ∈ Xs, IsRSet M r X := by
    intro X hX
    obtain ⟨hXr, hne⟩ := mem_diffR.1 (hD X hX)
    have hM : M ∉ X := fun hM => hne (by simp [posF, hM])
    exact isRSet_of_not_mem hXr hM
  have hXsM' : ∀ i, ∀ X ∈ Xs.take i, IsRSet M r X := fun i X hX => hXsM X (List.mem_of_mem_take hX)
  have hfw : FlipWalkR M r (IsSignotopeR M r) u Xs := by
    refine ⟨hXsM, fun i hi => fibre_forward hr ?_⟩
    rw [posF_flipsR u (hXsM' i)]
    exact hpre i hi
  have hend' : AgreeR M r (flipsR u Xs) v := by
    intro X hX
    have hM : M ∉ X := fun h => Nat.lt_irrefl M (hX.2.2 M h)
    have h1 := hend X (hX.mono (Nat.le_succ M))
    rw [← posF_flipsR u hXsM] at h1
    simpa [posF, hM] using h1
  have := flips_to_rwalk hfw hend'
  rwa [hlen] at this

end OMDistance
