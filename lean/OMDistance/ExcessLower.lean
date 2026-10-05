import OMDistance.MinorLift
import OMDistance.LiftHamming
import OMDistance.Sheet

/-!
# Proposition 8.5, the lower bound

For every walk of chirotopes of length `ℓ` from `Pos_r(L s)` to `Pos_r(L t)` on `N ∪ S ∪ {∞}` there is a walk of
chirotopes of length `k` from `Pos₃ s` to `Pos₃ t` on `S ∪ {∞}` with `λ (k - h) ≤ ℓ - H`, i.e.
`λ k + H ≤ ℓ + λ h`, where `λ = binom(c, q)`, `h = |D(s, t)|`, `H = |D(L s, L t)|`.

Proof: let `Xs` be the flipped bases.  For each `q`-subset `Y ⊆ N` the minors `χ_Y` of the terms form a walk of
chirotopes from `(Pos_r L s)_Y = Pos₃ s` to `Pos₃ t` with one step for each flip of a basis `B` with `B ∩ N = Y`
(Lemma 6.6: `rwalk_pullback`, `minorY_chirotope`, `minorY_posF_lift`).  The bases with `|B ∩ N| ≠ q` are flipped at
least as often as there are such bases in `D(L s, L t)` (Lemma 2.5: `diffR_filter_le`), and
`H = λ h + #{B ∈ D(L s, L t) : |B ∩ N| ≠ q}` (`hamR_lift_split`).  Taking for `Y` a set with fewest flips
(`exists_mul_le_sum`) and counting all flips (`partition_flips`) gives the bound.
-/

namespace OMDistance

private theorem sum_map_add_of {α : Type} {L : List α} {f g h : α → Nat} (H : ∀ y ∈ L, f y = g y + h y) :
    (L.map f).sum = (L.map g).sum + (L.map h).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [H a List.mem_cons_self, ih (fun y hy => H y (List.mem_cons_of_mem _ hy))]
    omega

private theorem sum_indicator (L : List (List Nat)) (Y0 : List Nat) (hnd : L.Nodup) :
    (L.map fun Y => if Y0 = Y then 1 else 0).sum = if Y0 ∈ L then 1 else 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, ih hnd.2, List.mem_cons]
    by_cases h : Y0 = a
    · subst h; simp [hnd.1]
    · simp [h]

private theorem sum_map_zero {α : Type} (L : List α) : (L.map fun _ => (0 : Nat)).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]

/-- Every flipped basis `B` (an `r`-subset of `[c + m + 1]`, `r = q + 3`) either has `|B ∩ N| ≠ q` or lies in the
image of the minor relabelling of exactly one `q`-subset `Y = B ∩ N` of `N = [c]`. -/
theorem partition_flips {c m q : Nat} (Xs : List (List Nat)) (hXs : ∀ X ∈ Xs, IsRSet (c + m + 1) (q + 3) X) :
    ((rsets c q).map fun Y => (preimages (m + 1) 3 (fun Z => Y ++ Z.map (· + c)) Xs).length).sum +
      (Xs.filter fun B => (B.filter fun x => decide (x < c)).length != q).length = Xs.length := by
  induction Xs with
  | nil =>
    simp only [preimages, List.filterMap_nil, List.length_nil, List.filter_nil, Nat.add_zero]
    exact sum_map_zero _
  | cons B Xs ih =>
    have ih := ih (fun X hX => hXs X (List.mem_cons_of_mem _ hX))
    have hB : IsRSet (c + (m + 1)) (q + 3) B := hXs B List.mem_cons_self
    have key : ∀ Y ∈ rsets c q, (preimages (m + 1) 3 (fun Z => Y ++ Z.map (· + c)) (B :: Xs)).length =
        (if B.filter (fun x => decide (x < c)) = Y then 1 else 0) +
          (preimages (m + 1) 3 (fun Z => Y ++ Z.map (· + c)) Xs).length := by
      intro Y hY
      rw [length_preimages, length_preimages, List.filter_cons]
      have hiff := minor_image_iff (M := m + 1) (r := 3) (mem_rsets.1 hY) hB
      by_cases h : B.filter (fun x => decide (x < c)) = Y
      · rw [ite_eq_left (hiff.2 h), ite_eq_left h, List.length_cons]
        omega
      · have hf : ((rsets (m + 1) 3).any fun Z => (Y ++ Z.map (· + c)) == B) = false := by
          cases e : ((rsets (m + 1) 3).any fun Z => (Y ++ Z.map (· + c)) == B) with
          | false => rfl
          | true => exact absurd (hiff.1 e) h
        rw [hf, ite_eq_right h]
        simp
    rw [sum_map_add_of key, sum_indicator _ _ (rsets_nodup c q), List.filter_cons, List.length_cons]
    by_cases hq : (B.filter fun x => decide (x < c)).length = q
    · have hY0 : B.filter (fun x => decide (x < c)) ∈ rsets c q := by
        refine mem_rsets.2 ⟨hq, hB.2.1.sublist List.filter_sublist, fun x hx => ?_⟩
        have := (List.mem_filter.1 hx).2
        simpa using this
      have hne : ((B.filter fun x => decide (x < c)).length != q) = false := by simp [hq]
      rw [ite_eq_left hY0, hne]
      simp only [Bool.false_eq_true, ite_false]
      omega
    · have hY0 : B.filter (fun x => decide (x < c)) ∉ rsets c q := fun h => hq (mem_rsets.1 h).1
      have hne : ((B.filter fun x => decide (x < c)).length != q) = true := by simp [hq]
      rw [ite_eq_right hY0, hne, ite_eq_left rfl, List.length_cons]
      omega

/-- Some term of a nonempty list is at most the average. -/
theorem exists_mul_le_sum {α : Type} (L : List α) (hL : L ≠ []) (f : α → Nat) :
    ∃ y ∈ L, L.length * f y ≤ (L.map f).sum := by
  induction L with
  | nil => exact absurd rfl hL
  | cons a L ih =>
    by_cases hL' : L = []
    · subst hL'
      exact ⟨a, List.mem_cons_self, by simp⟩
    · obtain ⟨y, hy, hle⟩ := ih hL'
      by_cases hay : f a ≤ f y
      · refine ⟨a, List.mem_cons_self, ?_⟩
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := Nat.mul_le_mul_left L.length hay
        rw [Nat.succ_mul]
        omega
      · refine ⟨y, List.mem_cons_of_mem _ hy, ?_⟩
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        rw [Nat.succ_mul]
        omega

/-- Proposition 8.5, lower bound. -/
theorem excess_lower {m c q : Nat} (hm : 3 ≤ m) (hc : q ≤ c) {s t : SignMap} {ℓ : Nat}
    (hw : ChiroWalk (c + m + 1) (q + 3) (posF (c + m) (lift c s)) (posF (c + m) (lift c t)) ℓ) :
    ∃ k, ChiroWalk (m + 1) 3 (posF m s) (posF m t) k ∧
      binom c q * k + hamR (c + m) (q + 3) (lift c s) (lift c t) ≤ ℓ + binom c q * hamR m 3 s t := by
  obtain ⟨Xs, hlen, hfw, hend⟩ := rwalk_to_flips (isChirotope_agreeInv _ _) hw
  -- the minor walks
  have hminor : ∀ Y, IsRSet c q Y → ChiroWalk (m + 1) 3 (posF m s) (posF m t)
      (preimages (m + 1) 3 (fun Z => Y ++ Z.map (· + c)) Xs).length := by
    intro Y hY
    have hφ : Relabel (m + 1) 3 (c + m + 1) (q + 3) (fun Z => Y ++ Z.map (· + c)) := relabel_minor hY
    have hPQ : ∀ u, IsChirotope (c + m + 1) (q + 3) u →
        IsChirotope (m + 1) 3 (fun Z => u (Y ++ Z.map (· + c))) :=
      fun u hu => minorY_chirotope (M := m + 1) hY (by decide) (by omega) hu
    have hw' := rwalk_pullback hφ hPQ (isChirotope_agreeInv _ _) hfw hend
    exact (hw'.congr_start (isChirotope_agreeInv _ _) (minorY_posF_lift s hY)).congr_finish
      (minorY_posF_lift t hY)
  have hne : rsets c q ≠ [] := by
    intro h
    have h1 := length_rsets c q
    have h2 := binom_pos hc
    rw [h] at h1
    simp only [List.length_nil] at h1
    omega
  obtain ⟨Y, hY, hYmin⟩ := exists_mul_le_sum (rsets c q) hne
    (fun Y => (preimages (m + 1) 3 (fun Z => Y ++ Z.map (· + c)) Xs).length)
  rw [length_rsets] at hYmin
  refine ⟨_, hminor Y (mem_rsets.1 hY), ?_⟩
  have hpart := partition_flips Xs hfw.1
  have hfil := diffR_filter_le hend (fun B => (B.filter fun x => decide (x < c)).length != q)
  rw [diffR_posF] at hfil
  have hsplit := hamR_lift_split m c q s t
  omega

end OMDistance
