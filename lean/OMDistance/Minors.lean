import OMDistance.ChiroBasic
import OMDistance.Pullback

/-!
# Minors of chirotopes (Lemma 6.5, the parts that are needed)

All minors are written on ground sets of the form `[M']`, relabelled in increasing order.

* **Restriction / deletion** (`restrictR z χ`): the restriction of `χ` to the elements of an increasing list `z`,
  relabelled `0, …, z.length - 1`.  Deleting elements is restricting to the others.
* **Contraction of the minimum** (`contract0 χ`): `(χ/0)(Y) = χ(0, y₁, …, y_{r-1})` for `Y = {y₁ < ⋯}` in
  `[M+1] ∖ {0}`, relabelled `y ↦ y - 1`.  Since `0` is the minimum, the tuple `(0, y₁, …)` is increasing, so no sign
  appears.
* **The minor `χ_Y` of Proposition 8.5** (`minorY c Y χ`): for a `q`-subset `Y` of `[c]`, contract the elements of
  `Y` one by one (each is the minimum at that moment) and delete the other elements of `[c]`:
  `χ_Y(Z) = χ(Y ++ (Z + c))` for a set `Z` of the remaining ground set `[M]` (element `z` of `[M]` is `z + c`).

Each is a uniform chirotope (of rank `r`, `r - 1`, `r` respectively); in set form, (GP) of the minor at `σ'` is
(GP) of `χ` at the corresponding larger `σ`.
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- The restriction of `χ` to the elements of the increasing list `z`, relabelled by `[z.length]`. -/
def restrictR (z : List Nat) (χ : SignMap) : SignMap := fun X => χ (X.map fun i => z.getD i 0)

/-- The contraction of the minimum element `0`, relabelled `y ↦ y - 1`. -/
def contract0 (χ : SignMap) : SignMap := fun X => χ (0 :: X.map (· + 1))

/-- The minor `χ_Y`: contract the elements of `Y ⊆ [c]` and delete the rest of `[c]`; the element `z` of the new
ground set is the old element `z + c`. -/
def minorY (c : Nat) (Y : List Nat) (χ : SignMap) : SignMap := fun Z => χ (Y ++ Z.map (· + c))

/-- `g` is strictly increasing on `[N]`. -/
private def MonoOn (N : Nat) (g : Nat → Nat) : Prop := ∀ i j, i < j → j < N → g i < g j

private theorem MonoOn.inj {N : Nat} {g : Nat → Nat} (hg : MonoOn N g) {i j : Nat} (hi : i < N) (hj : j < N)
    (h : g i = g j) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := hg i j hij hj; omega
  · exact hij
  · have := hg j i hij hi; omega

/-- Sorting commutes with a map that is strictly increasing on the entries. -/
private theorem map_isort_strictIncr {N : Nat} {g : Nat → Nat} (hg : MonoOn N g) {m : List Nat} (hm : m.Nodup)
    (hmN : ∀ x ∈ m, x < N) : StrictIncr ((isort m).map g) := by
  have hs := isort_strictIncr hm
  unfold StrictIncr at hs ⊢
  rw [List.pairwise_map]
  have hs' : (isort m).Pairwise (fun a b => a < b ∧ b < N) := by
    refine List.Pairwise.imp_of_mem ?_ hs
    intro a b _ hb hab
    exact ⟨hab, hmN b (mem_isort.1 hb)⟩
  exact hs'.imp (fun h => hg _ _ h.1 h.2)

private theorem nodup_map_of_monoOn {N : Nat} {g : Nat → Nat} (hg : MonoOn N g) {m : List Nat} (hm : m.Nodup)
    (hmN : ∀ x ∈ m, x < N) : (m.map g).Nodup := by
  induction m with
  | nil => simp
  | cons a m ih =>
    rw [List.nodup_cons] at hm
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih hm.2 (fun x hx => hmN x (by simp [hx]))⟩
    obtain ⟨b, hb, hba⟩ := List.mem_map.1 h
    have := hg.inj (hmN b (by simp [hb])) (hmN a (by simp)) hba
    subst this
    exact hm.1 hb

/-- The general minor: fix a set `P` below the image of `g` and relabel `[N]` by `g`, strictly increasing on
`[N]`; the map `X ↦ χ (P ++ X.map g)` is a uniform chirotope of rank `r` on `[N]` if `χ` is one of rank
`q + r` on `[K]`. -/
private theorem minorGen_chirotope {K N q r : Nat} {P : List Nat} (hP : IsRSet K q P) {g : Nat → Nat}
    (hg : MonoOn N g) (hgK : ∀ i < N, g i < K) (hPg : ∀ p ∈ P, ∀ i < N, p < g i) (hr : 2 ≤ r) (hrN : r ≤ N)
    {χ : SignMap} (hχ : IsChirotope K (q + r) χ) : IsChirotope N r (fun X => χ (P ++ X.map g)) := by
  rw [isChirotope_iff_set] at hχ ⊢
  obtain ⟨_, hqK, hχ⟩ := hχ
  refine ⟨hr, hrN, fun σ' hσ' d hd c hcd b hbc a hab ha hb hc hdσ => ?_⟩
  have hσN : ∀ x ∈ σ', x < N := hσ'.2.2
  let σ := P ++ σ'.map g
  have hσ : IsRSet K (q + r - 2) σ := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [σ, List.length_append, List.length_map, hP.1, hσ'.1]; omega
    · unfold StrictIncr
      rw [List.pairwise_append]
      refine ⟨hP.2.1, ?_, ?_⟩
      · have := map_isort_strictIncr hg hσ'.nodup hσN
        rwa [isort_of_strictIncr hσ'.2.1] at this
      · intro p hp y hy
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
        exact hPg p hp i (hσN i hi)
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hP.2.2 x hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        exact hgK i (hσN i hi)
  have hout : ∀ x, x < N → x ∉ σ' → g x ∉ σ := by
    intro x hx hxσ hm
    rcases List.mem_append.1 hm with hm | hm
    · have := hPg _ hm x hx; omega
    · obtain ⟨i, hi, hgi⟩ := List.mem_map.1 hm
      have := hg.inj (hσN i hi) hx hgi
      subst this
      exact hxσ hi
  have key : ∀ x y, x < N → y < N → x ≠ y → x ∉ σ' → y ∉ σ' →
      setVal (fun X => χ (P ++ X.map g)) σ' x y = setVal χ σ (g x) (g y) := by
    intro x y hx hy hxy hxσ hyσ
    unfold setVal
    have hlN : ∀ w ∈ σ' ++ [x, y], w < N := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hσN w hw
      · simp at hw; rcases hw with rfl | rfl <;> assumption
    have hlnd : (σ' ++ [x, y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hσ'.nodup, by simp [hxy], ?_⟩
      intro u hu v hv
      simp at hv
      rcases hv with rfl | rfl
      · intro h; subst h; exact hxσ hu
      · intro h; subst h; exact hyσ hu
    have heq : σ ++ [g x, g y] = P ++ (σ' ++ [x, y]).map g := by
      simp [σ, List.map_append, List.append_assoc]
    show χ (P ++ (isort (σ' ++ [x, y])).map g) = χ (isort (σ ++ [g x, g y]))
    rw [heq]
    congr 1
    symm
    apply isort_eq
    · unfold StrictIncr
      rw [List.pairwise_append]
      refine ⟨hP.2.1, map_isort_strictIncr hg hlnd hlN, ?_⟩
      intro p hp w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
      exact hPg p hp i (hlN i (mem_isort.1 hi))
    · rw [List.nodup_append]
      refine ⟨hP.nodup, nodup_map_of_monoOn hg hlnd hlN, ?_⟩
      intro p hp w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
      have := hPg p hp i (hlN i hi)
      omega
    · intro w
      simp only [List.mem_append, List.mem_map, mem_isort]
  have hdN := hd
  have hcN : c < N := by omega
  have hbN : b < N := by omega
  have haN : a < N := by omega
  have := hχ σ hσ (g d) (hgK d hdN) (g c) (hg c d hcd hdN) (g b) (hg b c hbc hcN) (g a) (hg a b hab hbN)
    (hout a haN ha) (hout b hbN hb) (hout c hcN hc) (hout d hdN hdσ)
  unfold GPSet at this ⊢
  rw [key a b haN hbN (by omega) ha hb, key a c haN hcN (by omega) ha hc, key a d haN hdN (by omega) ha hdσ,
    key b c hbN hcN (by omega) hb hc, key b d hbN hdN (by omega) hb hdσ, key c d hcN hdN (by omega) hc hdσ]
  exact this

/-- Lemma 6.5 (restriction): the restriction of a uniform chirotope of rank `r` to at least `r` elements is a
uniform chirotope of rank `r`. -/
theorem restrictR_chirotope {M r : Nat} {z : List Nat} (hz : StrictIncr z) (hzM : ∀ x ∈ z, x < M)
    (hr : r ≤ z.length) {χ : SignMap} (hχ : IsChirotope M r χ) : IsChirotope z.length r (restrictR z χ) := by
  have hg : MonoOn z.length (fun i => z.getD i 0) := by
    intro i j hij hj
    have hi : i < z.length := Nat.lt_trans hij hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some]
    exact List.pairwise_iff_getElem.1 hz i j hi hj hij
  have hgK : ∀ i < z.length, z.getD i 0 < M := by
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hzM _ (List.getElem_mem hi)
  have hP : IsRSet M 0 [] := ⟨rfl, List.Pairwise.nil, by simp⟩
  have hχ' : IsChirotope M (0 + r) χ := by rw [Nat.zero_add]; exact hχ
  exact minorGen_chirotope hP hg hgK (by simp) hχ.1 hr hχ'

/-- Lemma 6.5 (contraction): contracting the minimum element of a uniform chirotope of rank `r ≥ 3` gives a
uniform chirotope of rank `r - 1`. -/
theorem contract0_chirotope {M r : Nat} (hr : 3 ≤ r) {χ : SignMap} (hχ : IsChirotope (M + 1) r χ) :
    IsChirotope M (r - 1) (contract0 χ) := by
  have hY : IsRSet 1 1 [0] := ⟨rfl, by simp [StrictIncr], by simp⟩
  have hχ' : IsChirotope (1 + M) (1 + (r - 1)) χ := by
    rw [Nat.add_comm 1 M, show 1 + (r - 1) = r by omega]; exact hχ
  have hg : MonoOn M (· + 1) := fun i j hij _ => by simp only; omega
  exact minorGen_chirotope (hY.mono (Nat.le_add_right 1 M)) hg (fun i hi => by omega)
    (fun p hp i _ => by simp at hp; omega) (by omega) (by have := hχ.2.1; omega) hχ'

/-- The minor `χ_Y` of a uniform chirotope of rank `q + r` on `[c + M]` is a uniform chirotope of rank `r` on
`[M]` (Lemma 6.5, applied `q` times for contraction and then for deletion). -/
theorem minorY_chirotope {c q M r : Nat} {Y : List Nat} (hY : IsRSet c q Y) (hr : 2 ≤ r) (hrM : r ≤ M)
    {χ : SignMap} (hχ : IsChirotope (c + M) (q + r) χ) : IsChirotope M r (minorY c Y χ) := by
  have hg : MonoOn M (· + c) := fun i j hij _ => by simp only; omega
  have hgK : ∀ i < M, i + c < c + M := fun i hi => by omega
  have hPg : ∀ p ∈ Y, ∀ i < M, p < i + c := fun p hp i _ => by have := hY.2.2 p hp; omega
  exact minorGen_chirotope (hY.mono (Nat.le_add_right c M)) hg hgK hPg hr hrM hχ

end OMDistance
