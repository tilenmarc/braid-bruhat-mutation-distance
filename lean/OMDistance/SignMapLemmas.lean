import OMDistance.RSets

/-!
# Sign maps: agreement, flips, negation and the Hamming distance

General facts about `AgreeR`, `flipR`, `flipsR`, `negR`, `diffR`, `hamR` and `DiffersInOneR` for sign maps of any
rank on `[M]`.
-/

namespace OMDistance

theorem AgreeR.refl (M r : Nat) (u : SignMap) : AgreeR M r u u := fun _ _ => rfl

theorem AgreeR.symm {M r : Nat} {u v : SignMap} (h : AgreeR M r u v) : AgreeR M r v u :=
  fun X hX => (h X hX).symm

theorem AgreeR.trans {M r : Nat} {u v w : SignMap} (h₁ : AgreeR M r u v) (h₂ : AgreeR M r v w) :
    AgreeR M r u w :=
  fun X hX => (h₁ X hX).trans (h₂ X hX)

theorem flipR_self (u : SignMap) (X : List Nat) : flipR u X X = !u X := by
  simp [flipR]

theorem flipR_ne (u : SignMap) {X Y : List Nat} (h : Y ≠ X) : flipR u X Y = u Y := by
  simp [flipR, h]

theorem flipsR_nil (u : SignMap) : flipsR u [] = u := rfl

theorem flipsR_cons (u : SignMap) (X : List Nat) (Xs : List (List Nat)) :
    flipsR u (X :: Xs) = flipsR (flipR u X) Xs := rfl

theorem flipsR_append (u : SignMap) (Xs Ys : List (List Nat)) :
    flipsR u (Xs ++ Ys) = flipsR (flipsR u Xs) Ys := by
  simp [flipsR, List.foldl_append]

/-- The value of `flipsR u Xs` at `Y`: negated iff `Y` is flipped an odd number of times. -/
theorem flipsR_apply (u : SignMap) (Xs : List (List Nat)) (Y : List Nat) :
    flipsR u Xs Y = if Xs.count Y % 2 = 0 then u Y else !u Y := by
  induction Xs generalizing u with
  | nil => simp [flipsR]
  | cons X Xs ih =>
    rw [flipsR_cons, ih, List.count_cons]
    by_cases h : Y = X
    · subst h
      have hf : flipR u Y Y = !u Y := flipR_self u Y
      simp only [beq_self_eq_true, ite_true, hf]
      by_cases hc : Xs.count Y % 2 = 0
      · have : ¬ (Xs.count Y + 1) % 2 = 0 := by omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false this)]
      · have : (Xs.count Y + 1) % 2 = 0 := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_left_of_eq_true _ _ (eq_true this), Bool.not_not]
    · have h' : ¬ (X == Y) = true := fun hb => h (beq_iff_eq.1 hb).symm
      rw [flipR_ne u h, ite_eq_right_of_eq_false _ _ (eq_false h'), Nat.add_zero]

theorem flipsR_congr {M r : Nat} {u u' : SignMap} (h : AgreeR M r u u') (Xs : List (List Nat)) :
    AgreeR M r (flipsR u Xs) (flipsR u' Xs) := by
  intro X hX
  rw [flipsR_apply, flipsR_apply, h X hX]

theorem mem_diffR {M r : Nat} {u v : SignMap} {X : List Nat} :
    X ∈ diffR M r u v ↔ IsRSet M r X ∧ u X ≠ v X := by
  simp [diffR, List.mem_filter, mem_rsets]

theorem diffR_nodup (M r : Nat) (u v : SignMap) : (diffR M r u v).Nodup := by
  exact (rsets_nodup M r).filter _

theorem hamR_congr {M r : Nat} {u u' v v' : SignMap} (hu : AgreeR M r u u') (hv : AgreeR M r v v') :
    hamR M r u v = hamR M r u' v' := by
  unfold hamR diffR
  congr 1
  apply List.filter_congr
  intro X hX
  have hX' := mem_rsets.1 hX
  rw [hu X hX', hv X hX']

theorem hamR_comm (M r : Nat) (u v : SignMap) : hamR M r u v = hamR M r v u := by
  unfold hamR diffR
  congr 1
  apply List.filter_congr
  intro X _
  cases u X <;> cases v X <;> rfl

/-- The Hamming distance is at most the number of `r`-subsets. -/
theorem hamR_le_binom (M r : Nat) (u v : SignMap) : hamR M r u v ≤ binom M r := by
  rw [← length_rsets M r]
  exact List.length_filter_le _ _

private theorem length_filter_add_not {α : Type} (L : List α) (p q : α → Bool) (h : ∀ x, p x = !q x) :
    (L.filter p).length + (L.filter q).length = L.length := by
  induction L with
  | nil => rfl
  | cons X L ih =>
    rw [List.filter_cons, List.filter_cons, h X]
    cases q X
    · simp only [Bool.not_false, ite_true, List.length_cons]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, List.length_cons]
      omega

private theorem filter_ne_neg_add (L : List (List Nat)) (u v : SignMap) :
    (L.filter fun X => u X != negR v X).length + (L.filter fun X => u X != v X).length = L.length :=
  length_filter_add_not L _ _ fun X => by simp only [negR]; cases u X <;> cases v X <;> rfl

/-- `u` and `-v` differ exactly where `u` and `v` agree. -/
theorem hamR_negR (M r : Nat) (u v : SignMap) : hamR M r u (negR v) + hamR M r u v = binom M r := by
  rw [← length_rsets M r]
  exact filter_ne_neg_add (rsets M r) u v

theorem negR_negR (u : SignMap) : negR (negR u) = u := by
  funext X; simp [negR]

theorem negR_flipR (u : SignMap) (X : List Nat) : negR (flipR u X) = flipR (negR u) X := by
  funext Y; by_cases h : Y = X <;> simp [negR, flipR, h]

theorem AgreeR.negR {M r : Nat} {u v : SignMap} (h : AgreeR M r u v) : AgreeR M r (negR u) (negR v) :=
  fun X hX => by simp [OMDistance.negR, h X hX]

/-- An edge `u — v` is a flip of one `r`-set. -/
theorem differsInOneR_iff {M r : Nat} {u v : SignMap} :
    DiffersInOneR M r u v ↔ ∃ X, IsRSet M r X ∧ AgreeR M r (flipR u X) v := by
  constructor
  · rintro ⟨X, hX, hne, hrest⟩
    refine ⟨X, hX, fun Y hY => ?_⟩
    by_cases h : Y = X
    · subst h
      rw [flipR_self]
      cases hu : u Y <;> cases hv : v Y <;> simp_all
    · rw [flipR_ne u h]
      exact hrest Y hY h
  · rintro ⟨X, hX, hag⟩
    refine ⟨X, hX, ?_, fun Y hY h => ?_⟩
    · rw [← hag X hX, flipR_self]
      cases u X <;> simp
    · rw [← hag Y hY, flipR_ne u h]

theorem differsInOneR_flipR {M r : Nat} (u : SignMap) {X : List Nat} (hX : IsRSet M r X) :
    DiffersInOneR M r u (flipR u X) := by
  exact differsInOneR_iff.2 ⟨X, hX, AgreeR.refl M r _⟩

theorem DiffersInOneR.negR {M r : Nat} {u v : SignMap} (h : DiffersInOneR M r u v) :
    DiffersInOneR M r (OMDistance.negR u) (OMDistance.negR v) := by
  obtain ⟨X, hX, hne, hrest⟩ := h
  refine ⟨X, hX, ?_, fun Y hY hYX => ?_⟩
  · simp only [OMDistance.negR]
    cases hu : u X <;> cases hv : v X <;> simp_all
  · simp [OMDistance.negR, hrest Y hY hYX]

theorem DiffersInOneR.congr {M r : Nat} {u u' v v' : SignMap} (h : DiffersInOneR M r u v)
    (hu : AgreeR M r u u') (hv : AgreeR M r v v') : DiffersInOneR M r u' v' := by
  obtain ⟨X, hX, hne, hrest⟩ := h
  refine ⟨X, hX, ?_, fun Y hY hYX => ?_⟩
  · rw [← hu X hX, ← hv X hX]; exact hne
  · rw [← hu Y hY, ← hv Y hY]; exact hrest Y hY hYX

end OMDistance
