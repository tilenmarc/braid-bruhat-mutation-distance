import OMDistance.Minors
import OMDistance.Lift
import OMDistance.Signotope

/-!
# The minors of the lifted positive fibre (proof of Proposition 8.5)

For a `q`-set `Y = {y₁ < ⋯ < y_q} ⊆ N` and `χ` on `N ∪ S ∪ {∞}`, the minor `χ_Y` (contract `y₁, …, y_q` in turn,
delete `N ∖ Y`) is `χ_Y(Z) = χ(y₁, …, y_q, z₁, z₂, z₃)` for `Z = {z₁ < z₂ < z₃} ⊆ S ∪ {∞}`; the tuple is increasing
since `N < S < ∞`.  For `χ = Pos_r(L s)` this is `+` if `∞ ∈ Z` and `s(top(Y ∪ Z)) = s(Z)` otherwise, so
`(Pos_r L s)_Y = Pos₃ s`.

0-based: `N = [c]`, `S ∪ {∞} = {c, …, c+m}`, and `Z ⊆ [m+1]` stands for `Z + c`; `χ_Y = minorY c Y χ`.
-/

namespace OMDistance

theorem minorY_posF_lift {m c q : Nat} (s : SignMap) {Y : List Nat} (hY : IsRSet c q Y) :
    AgreeR (m + 1) 3 (minorY c Y (posF (c + m) (lift c s))) (posF m s) := by
  intro X hX
  have hYc : ∀ y ∈ Y, y < c := hY.2.2
  have hmem : (c + m ∈ Y ++ X.map (· + c)) ↔ m ∈ X := by
    constructor
    · intro h
      rcases List.mem_append.1 h with h | h
      · have := hYc _ h; omega
      · obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h
        have : x = m := by omega
        exact this ▸ hx
    · intro h
      exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨m, h, by omega⟩))
  have hfilt : (Y ++ X.map (· + c)).filter (fun x => decide (c ≤ x)) = X.map (· + c) := by
    rw [List.filter_append]
    have h1 : Y.filter (fun x => decide (c ≤ x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy; have := hYc y hy; simp; omega
    have h2 : (X.map (· + c)).filter (fun x => decide (c ≤ x)) = X.map (· + c) := by
      rw [List.filter_eq_self]
      intro x hx
      obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx
      simp
    rw [h1, h2]; rfl
  have hlen : (X.map (· + c)).length = 3 := by rw [List.length_map]; exact hX.1
  have hdrop : (Y ++ X.map (· + c)).drop ((Y ++ X.map (· + c)).length - 3) = X.map (· + c) := by
    rw [List.length_append, hlen, Nat.add_sub_cancel, List.drop_left]
  have hback : (X.map (· + c)).map (· - c) = X := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id X]
    apply List.map_congr_left
    intro x _
    simp
  unfold minorY posF
  by_cases hm : m ∈ X
  · simp only [hmem.2 hm, hm, ite_true]
  · have hm' : c + m ∉ Y ++ X.map (· + c) := fun h => hm (hmem.1 h)
    simp only [hm', hm, ite_false]
    unfold lift
    simp only [hfilt, hlen, Nat.le_refl, ite_true, hdrop, hback]

end OMDistance
