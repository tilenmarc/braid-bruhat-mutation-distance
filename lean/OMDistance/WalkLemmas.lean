import OMDistance.Parity

/-!
# Walks as flip lists

A walk `RWalk M r P u v k` (every map satisfies `P`, consecutive maps differ in one `r`-set) is the same as a list
`Xs` of `k` flipped valid `r`-sets from `u` all of whose prefixes give maps satisfying `P`, ending at a map
agreeing with `v` (`FlipWalkR`).  This needs `P` to depend only on the values on `r`-subsets of `[M]`
(`AgreeInv`), which holds for chirotopes and signotopes.
-/

namespace OMDistance

/-- `P` depends only on the values on the `r`-subsets of `[M]`. -/
def AgreeInv (M r : Nat) (P : SignMap → Prop) : Prop := ∀ u u', AgreeR M r u u' → P u → P u'

/-- A walk of maps satisfying `P`, given by its start `s` and the list `Xs` of flipped `r`-sets. -/
def FlipWalkR (M r : Nat) (P : SignMap → Prop) (s : SignMap) (Xs : List (List Nat)) : Prop :=
  (∀ X ∈ Xs, IsRSet M r X) ∧ ∀ i, i ≤ Xs.length → P (flipsR s (Xs.take i))

private theorem flipR_congr' {M r : Nat} {u u' : SignMap} (h : AgreeR M r u u') (X : List Nat) :
    AgreeR M r (flipR u X) (flipR u' X) := by
  intro Y hY
  by_cases hYX : Y = X
  · subst hYX; rw [flipR_self, flipR_self, h Y hY]
  · rw [flipR_ne u hYX, flipR_ne u' hYX, h Y hY]

private theorem flipsR_congr' {M r : Nat} {u u' : SignMap} (h : AgreeR M r u u') (Xs : List (List Nat)) :
    AgreeR M r (flipsR u Xs) (flipsR u' Xs) := by
  induction Xs generalizing u u' with
  | nil => exact h
  | cons X Xs ih => rw [flipsR_cons, flipsR_cons]; exact ih (flipR_congr' h X)

private theorem differsInOneR_iff' {M r : Nat} {u v : SignMap} :
    DiffersInOneR M r u v ↔ ∃ X, IsRSet M r X ∧ AgreeR M r (flipR u X) v := by
  constructor
  · rintro ⟨X, hX, hne, hrest⟩
    refine ⟨X, hX, fun Y hY => ?_⟩
    by_cases hYX : Y = X
    · subst hYX
      rw [flipR_self]
      cases hu : u Y <;> cases hv : v Y <;> simp_all
    · rw [flipR_ne u hYX]; exact hrest Y hY hYX
  · rintro ⟨X, hX, hag⟩
    refine ⟨X, hX, ?_, fun Y hY hYX => ?_⟩
    · have := hag X hX
      rw [flipR_self] at this
      rw [← this]; cases u X <;> simp
    · have := hag Y hY
      rwa [flipR_ne u hYX] at this

private theorem differsInOneR_flipR' {M r : Nat} (u : SignMap) {X : List Nat} (hX : IsRSet M r X) :
    DiffersInOneR M r u (flipR u X) :=
  differsInOneR_iff'.2 ⟨X, hX, AgreeR.refl _ _ _⟩

private theorem DiffersInOneR.congr' {M r : Nat} {u u' v v' : SignMap} (h : DiffersInOneR M r u v)
    (hu : AgreeR M r u u') (hv : AgreeR M r v v') : DiffersInOneR M r u' v' := by
  obtain ⟨X, hX, hag⟩ := differsInOneR_iff'.1 h
  exact differsInOneR_iff'.2 ⟨X, hX, ((flipR_congr' hu X).symm.trans hag).trans hv⟩

theorem rwalk_to_flips {M r : Nat} {P : SignMap → Prop} (hP : AgreeInv M r P) {u v : SignMap} {k : Nat}
    (hw : RWalk M r P u v k) :
    ∃ Xs : List (List Nat), Xs.length = k ∧ FlipWalkR M r P u Xs ∧ AgreeR M r (flipsR u Xs) v := by
  induction hw with
  | nil hu huv => exact ⟨[], rfl, ⟨fun X h => by simp at h, fun i hi => by simpa [flipsR_nil] using hu⟩, huv⟩
  | @cons u v w k hu hd _ ih =>
    obtain ⟨Xs, hlen, ⟨hXs, hpre⟩, hend⟩ := ih
    obtain ⟨X, hX, hXv⟩ := differsInOneR_iff'.1 hd
    refine ⟨X :: Xs, by simp [hlen], ⟨?_, ?_⟩, ?_⟩
    · intro Y hY
      simp only [List.mem_cons] at hY
      rcases hY with rfl | hY
      · exact hX
      · exact hXs Y hY
    · intro i hi
      cases i with
      | zero => simpa [flipsR_nil] using hu
      | succ j =>
        simp only [List.take_succ_cons, flipsR_cons]
        simp only [List.length_cons] at hi
        exact hP _ _ (flipsR_congr' hXv.symm _) (hpre j (by omega))
    · rw [flipsR_cons]
      exact (flipsR_congr' hXv Xs).trans hend

theorem flips_to_rwalk {M r : Nat} {P : SignMap → Prop} {u v : SignMap} {Xs : List (List Nat)}
    (hw : FlipWalkR M r P u Xs) (hend : AgreeR M r (flipsR u Xs) v) : RWalk M r P u v Xs.length := by
  induction Xs generalizing u with
  | nil =>
    have hu : P u := by simpa [flipsR_nil] using hw.2 0 (Nat.zero_le _)
    exact RWalk.nil hu hend
  | cons X Xs ih =>
    obtain ⟨hXs, hpre⟩ := hw
    have hu : P u := by simpa [flipsR_nil] using hpre 0 (Nat.zero_le _)
    have hX : IsRSet M r X := hXs X (by simp)
    have hw' : FlipWalkR M r P (flipR u X) Xs := by
      refine ⟨fun Y hY => hXs Y (by simp [hY]), fun i hi => ?_⟩
      have := hpre (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, flipsR_cons] using this
    exact RWalk.cons hu (differsInOneR_flipR' u hX) (ih hw' (by simpa [flipsR_cons] using hend))

theorem RWalk.mono {M r : Nat} {P Q : SignMap → Prop} (hPQ : ∀ u, P u → Q u) {u v : SignMap} {k : Nat}
    (hw : RWalk M r P u v k) : RWalk M r Q u v k := by
  induction hw with
  | nil hu huv => exact RWalk.nil (hPQ _ hu) huv
  | cons hu hd _ ih => exact RWalk.cons (hPQ _ hu) hd ih

theorem RWalk.start {M r : Nat} {P : SignMap → Prop} {u v : SignMap} {k : Nat} (hw : RWalk M r P u v k) :
    P u := by
  cases hw with
  | nil h _ => exact h
  | cons h _ _ => exact h

/-- The last map of a walk satisfies `P`, hence so does every map agreeing with it. -/
theorem RWalk.finish {M r : Nat} {P : SignMap → Prop} (hP : AgreeInv M r P) {u v : SignMap} {k : Nat}
    (hw : RWalk M r P u v k) : P v := by
  induction hw with
  | nil hu huv => exact hP _ _ huv hu
  | cons _ _ _ ih => exact ih

theorem RWalk.congr_start {M r : Nat} {P : SignMap → Prop} (hP : AgreeInv M r P) {u u' v : SignMap} {k : Nat}
    (hw : RWalk M r P u v k) (hu : AgreeR M r u u') : RWalk M r P u' v k := by
  cases hw with
  | nil h h' => exact RWalk.nil (hP _ _ hu h) (hu.symm.trans h')
  | cons h hd hw' => exact RWalk.cons (hP _ _ hu h) (hd.congr' hu (AgreeR.refl _ _ _)) hw'

theorem RWalk.congr_finish {M r : Nat} {P : SignMap → Prop} {u v v' : SignMap} {k : Nat}
    (hw : RWalk M r P u v k) (hv : AgreeR M r v v') : RWalk M r P u v' k := by
  induction hw with
  | nil hu huv => exact RWalk.nil hu (huv.trans hv)
  | cons hu hd _ ih => exact RWalk.cons hu hd (ih hv)

theorem RWalk.append {M r : Nat} {P : SignMap → Prop} (hP : AgreeInv M r P) {u v w : SignMap} {k l : Nat}
    (h₁ : RWalk M r P u v k) (h₂ : RWalk M r P v w l) : RWalk M r P u w (k + l) := by
  induction h₁ with
  | nil hu huv =>
    rw [Nat.zero_add]
    exact h₂.congr_start hP huv.symm
  | @cons u v' w' k hu hd _ ih =>
    rw [Nat.succ_add]
    exact RWalk.cons hu hd (ih h₂)

/-- A walk of length `k` has `k ≥ |D(u, v)|` (Lemma 2.5). -/
theorem RWalk.hamR_le {M r : Nat} {P : SignMap → Prop} {u v : SignMap} {k : Nat} (hw : RWalk M r P u v k) :
    hamR M r u v ≤ k := by
  have hw' : RWalk M r (fun _ => True) u v k := hw.mono (fun _ _ => trivial)
  obtain ⟨Xs, hlen, ⟨hXs, _⟩, hend⟩ := rwalk_to_flips (fun _ _ _ _ => trivial) hw'
  rw [← hlen]
  exact hamR_le_length hXs hend

end OMDistance
