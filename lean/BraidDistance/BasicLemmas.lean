import BraidDistance.Signotope

/-!
# General facts about triples, sign maps and the Hamming distance

Elementary lemmas used by many files: `Agree` is an equivalence relation compatible with flips and
restriction; membership in `triples` and `diffList`; the value of `flipList` (each flip of `t` negates the value
at `t`, so only the parity of the number of flips matters); signotopes and flip walks depend only on the values
at valid triples.
-/

namespace BraidDistance

theorem Agree.refl (m : Nat) (u : SMap) : Agree m u u := fun _ _ _ _ _ _ => rfl

theorem Agree.symm {m : Nat} {u v : SMap} (h : Agree m u v) : Agree m v u :=
  fun a b c h1 h2 h3 => (h a b c h1 h2 h3).symm

theorem Agree.trans {m : Nat} {u v w : SMap} (h₁ : Agree m u v) (h₂ : Agree m v w) : Agree m u w :=
  fun a b c h1 h2 h3 => (h₁ a b c h1 h2 h3).trans (h₂ a b c h1 h2 h3)

theorem Agree.at {m : Nat} {u v : SMap} (h : Agree m u v) {t : Triple} (ht : ValidTriple m t) :
    u.at t = v.at t :=
  h t.1 t.2.1 t.2.2 ht.1 ht.2.1 ht.2.2

theorem mem_triples {m : Nat} {t : Triple} : t ∈ triples m ↔ ValidTriple m t := by
  obtain ⟨a, b, c⟩ := t
  simp only [triples, List.mem_flatMap, List.mem_range, List.mem_range', List.mem_map, ValidTriple,
    Prod.mk.injEq]
  constructor
  · rintro ⟨_, h1, _, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨a, by omega, b, ⟨b - (a + 1), by omega, by omega⟩, c, ⟨c - (b + 1), by omega, by omega⟩,
      rfl, rfl, rfl⟩

theorem triples_nodup (m : Nat) : (triples m).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold triples
  rw [List.pairwise_flatMap]
  refine ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_flatMap]
    refine ⟨fun b _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      have := (List.nodup_iff_pairwise_ne).1 (List.nodup_range' (s := b + 1) (n := m - (b + 1)))
      refine this.imp ?_
      intro x y hxy h
      exact hxy (by simpa using h)
    · have := (List.nodup_iff_pairwise_ne).1 (List.nodup_range' (s := a + 1) (n := m - (a + 1)))
      refine this.imp ?_
      intro x y hxy p hp q hq h
      simp only [List.mem_map] at hp hq
      obtain ⟨_, _, rfl⟩ := hp
      obtain ⟨_, _, rfl⟩ := hq
      exact hxy (by simp at h; exact h.1)
  · have := (List.nodup_iff_pairwise_ne).1 (List.nodup_range (n := m))
    refine this.imp ?_
    intro x y hxy p hp q hq h
    simp only [List.mem_flatMap, List.mem_map] at hp hq
    obtain ⟨_, _, _, _, rfl⟩ := hp
    obtain ⟨_, _, _, _, rfl⟩ := hq
    exact hxy (by simp at h; exact h.1)

theorem mem_diffList {m : Nat} {u v : SMap} {t : Triple} :
    t ∈ diffList m u v ↔ ValidTriple m t ∧ u.at t ≠ v.at t := by
  unfold diffList
  rw [List.mem_filter, mem_triples]
  simp

theorem diffList_nodup (m : Nat) (u v : SMap) : (diffList m u v).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact ((List.nodup_iff_pairwise_ne).1 (triples_nodup m)).filter _

/-- Agreeing maps have the same Hamming distances. -/
theorem hamming_congr {m : Nat} {u u' v v' : SMap} (hu : Agree m u u') (hv : Agree m v v') :
    hamming m u v = hamming m u' v' := by
  unfold hamming diffList
  congr 1
  apply List.filter_congr
  intro t ht
  have ht := mem_triples.1 ht
  rw [Agree.at hu ht, Agree.at hv ht]

/-- The value of `flipList` at a triple: negated iff the triple occurs an odd number of times. -/
theorem flipList_at (u : SMap) (ts : List Triple) (t : Triple) :
    (flipList u ts).at t = (u.at t != (ts.count t % 2 == 1)) := by
  induction ts generalizing u with
  | nil => simp [flipList]
  | cons t' ts ih =>
    have h1 : flipList u (t' :: ts) = flipList (flipT u t') ts := rfl
    rw [h1, ih, List.count_cons]
    by_cases h : t' = t
    · subst h
      have : (flipT u t').at t' = !u.at t' := by simp [flipT, SMap.at]
      rw [this]
      simp only [beq_self_eq_true, ite_true]
      cases u.at t' <;> cases hc : (List.count t' ts % 2 == 1) <;> simp_all <;> omega
    · have : (flipT u t').at t = u.at t := by
        have h' : ¬ (t.1, t.2.1, t.2.2) = t' := fun h' => h h'.symm
        simp only [flipT, SMap.at, h', ite_false]
      rw [this]
      have : (t' == t) = false := by simpa using h
      simp [this]

theorem flipList_append (u : SMap) (ts ts' : List Triple) :
    flipList u (ts ++ ts') = flipList (flipList u ts) ts' := by
  unfold flipList; exact List.foldl_append

theorem flipList_congr {m : Nat} {u u' : SMap} (h : Agree m u u') (ts : List Triple) :
    Agree m (flipList u ts) (flipList u' ts) := by
  intro a b c h1 h2 h3
  have e1 := flipList_at u ts (a, b, c)
  have e2 := flipList_at u' ts (a, b, c)
  simp only [SMap.at] at e1 e2
  rw [e1, e2, h a b c h1 h2 h3]

theorem IsSignotope.congr {m : Nat} {u u' : SMap} (h : Agree m u u') (hu : IsSignotope m u) :
    IsSignotope m u' := by
  intro d hd c hc b hb a ha
  have hp : packet u' a b c d = packet u a b c d := by
    simp only [packet]
    rw [h a b c ha hb (by omega), h a b d ha (by omega) hd, h a c d (by omega) hc hd,
      h b c d hb hc hd]
  rw [hp]
  exact hu d hd c hc b hb a ha

theorem FlipWalk.congr {m : Nat} {s s' : SMap} {ts : List Triple} (h : Agree m s s')
    (hw : FlipWalk m s ts) : FlipWalk m s' ts :=
  ⟨hw.1, fun i hi => IsSignotope.congr (flipList_congr h _) (hw.2 i hi)⟩

/-- Flipping one valid triple: the maps differ exactly there. -/
theorem differsInOne_flipT {m : Nat} (u : SMap) {t : Triple} (ht : ValidTriple m t) :
    DiffersInOne m u (flipT u t) := by
  refine ⟨t, ht, ?_, ?_⟩
  · simp [flipT, SMap.at]
  · intro t' _ hne
    have h' : ¬ (t'.1, t'.2.1, t'.2.2) = t := hne
    simp only [flipT, SMap.at, h', ite_false]

end BraidDistance
