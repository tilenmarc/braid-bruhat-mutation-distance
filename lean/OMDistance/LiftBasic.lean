import OMDistance.OneStep

/-!
# The lift (Lemma 8.3)

`lift c s` is `L^r_N s` with `N = {0, …, c-1}` below `S = {c, …, c+m-1}` (the element `i` of `[m]` is `c + i`).

* `lift_congr`: the lift depends only on the values of `s` on 3-subsets of `[m]`.
* (a) The padding `lift c s` (rank 3) is a signotope (`padding_signotope`): a packet of a 4-set meeting `N` is
  `(+, +, +, x)`.  Adding a further element below gives the lift with one more new element and rank one higher:
  `L^{r+1}_{{ℓ} ∪ N} s = (L^r_N s)'` (`lift_succ`; in 0-based labels the old elements are shifted by one).  Hence
  `L^r_N s` is a signotope of rank `r` (`lift_signotope`, induction on `q = r - 3` with Lemma 8.1(a)).
* (b) If `T ∈ binom(S, 3)`, then `L s` and `L s^T` differ exactly on the sets `T ∪ Y`, `Y` a `q`-subset of
  `N ∪ {x ∈ S : x < min T}`; in 0-based labels `Y` is a `q`-subset of `[c + min T]` and the set is
  `Y ++ (T + c)` (`lift_diff`).
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-! ### Helpers: the top three elements of a set -/

/-- If at least `k` entries of an increasing list are `≥ c`, then its last `k` entries are `≥ c`. -/
private theorem drop_ge_of_filter {c k : Nat} : ∀ {X : List Nat}, StrictIncr X →
    k ≤ (X.filter fun x => decide (c ≤ x)).length → ∀ x ∈ X.drop (X.length - k), c ≤ x
  | [], _, _, x, hx => by simp at hx
  | a :: X, hX, hk, x, hx => by
    unfold StrictIncr at hX
    rw [List.pairwise_cons] at hX
    by_cases ha : c ≤ a
    · have hxm : x ∈ a :: X := (List.drop_sublist _ _).subset hx
      rcases List.mem_cons.1 hxm with rfl | hxm
      · exact ha
      · have := hX.1 x hxm; omega
    · have hf : ((a :: X).filter fun x => decide (c ≤ x)) = X.filter fun x => decide (c ≤ x) := by
        simp [ha]
      rw [hf] at hk
      have hle := List.length_filter_le (fun x => decide (c ≤ x)) X
      have e : (a :: X).length - k = (X.length - k) + 1 := by simp; omega
      rw [e, List.drop_succ_cons] at hx
      exact drop_ge_of_filter hX.2 hk x hx

private theorem len_ge_of_filter {c : Nat} {X : List Nat} (h : 3 ≤ (X.filter fun x => decide (c ≤ x)).length) :
    3 ≤ X.length :=
  Nat.le_trans h (List.length_filter_le _ _)

/-- The top three elements of `X`, translated back to `[m]`, form a 3-subset of `[m]`. -/
private theorem top_rset {c m r : Nat} {X : List Nat} (hX : IsRSet (c + m) r X)
    (h : 3 ≤ (X.filter fun x => decide (c ≤ x)).length) :
    IsRSet m 3 ((X.drop (X.length - 3)).map (· - c)) := by
  have hge := drop_ge_of_filter hX.2.1 h
  have hlen := len_ge_of_filter h
  refine ⟨by simp; omega, ?_, ?_⟩
  · unfold StrictIncr
    rw [List.pairwise_map]
    have hp : (X.drop (X.length - 3)).Pairwise (· < ·) := hX.2.1.sublist (List.drop_sublist _ _)
    have hp2 := List.Pairwise.and_mem.1 hp
    exact hp2.imp (fun {a b} hab => by
      have := hge a hab.1; have := hge b hab.2.1; have := hab.2.2; omega)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have := hge y hy
    have := hX.2.2 y ((List.drop_sublist _ _).subset hy)
    omega

private theorem lift_all_ge {c : Nat} (s : SignMap) {X : List Nat} (hX : ∀ x ∈ X, c ≤ x) (hl : X.length = 3) :
    lift c s X = s (X.map (· - c)) := by
  unfold lift
  have hf : (X.filter fun x => decide (c ≤ x)) = X := List.filter_eq_self.2 (by simpa using hX)
  rw [hf, hl]
  simp

private theorem lift_lt_cons {c a : Nat} (s : SignMap) (L : List Nat) (ha : a < c) (hL : L.length ≤ 2) :
    lift c s (a :: L) = true := by
  unfold lift
  have hf : ((a :: L).filter fun x => decide (c ≤ x)) = L.filter fun x => decide (c ≤ x) := by
    simp [List.filter_cons]; omega
  have := List.length_filter_le (fun x => decide (c ≤ x)) L
  rw [hf]
  split
  · omega
  · rfl

private theorem agreeInv_sig (M r : Nat) {u u' : SignMap} (hag : AgreeR M r u u') (hu : IsSignotopeR M r u) :
    IsSignotopeR M r u' := by
  intro P hP
  have e : rpacket u P = rpacket u' P := by
    unfold rpacket
    apply List.map_congr_left
    intro i hi
    rw [List.mem_reverse, List.mem_range, hP.1] at hi
    exact hag _ (hP.eraseIdx hi)
  rw [← e]
  exact hu P hP

theorem lift_congr {m c r : Nat} {s s' : SignMap} (h : AgreeR m 3 s s') :
    AgreeR (c + m) r (lift c s) (lift c s') := by
  intro X hX
  unfold lift
  split
  · next hc => exact h _ (top_rset hX hc)
  · rfl

/-- Lemma 8.3(a): the padding of a signotope is a signotope. -/
theorem padding_signotope {m c : Nat} {s : SignMap} (hs : IsSignotopeR m 3 s) :
    IsSignotopeR (c + m) 3 (lift c s) := by
  intro P hP
  obtain ⟨hlen, hinc, hlt⟩ := hP
  match P, hlen, hinc, hlt with
  | [a, b, d, e], _, hinc, hlt =>
  unfold StrictIncr at hinc
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hinc
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  show BraidDistance.oneChange [lift c s [a, b, d], lift c s [a, b, e], lift c s [a, d, e], lift c s [b, d, e]] = true
  by_cases ha : c ≤ a
  · rw [lift_all_ge s (by simp; omega) rfl, lift_all_ge s (by simp; omega) rfl,
      lift_all_ge s (by simp; omega) rfl, lift_all_ge s (by simp; omega) rfl]
    have := hs [a - c, b - c, d - c, e - c]
      ⟨rfl, by unfold StrictIncr; simp; omega, by simp; omega⟩
    exact this
  · rw [lift_lt_cons s _ (by omega) (by simp), lift_lt_cons s _ (by omega) (by simp),
      lift_lt_cons s _ (by omega) (by simp)]
    cases lift c s [b, d, e] <;> rfl

/-- Lemma 8.3(a): `L^{r+1}_{{ℓ} ∪ N} s = (L^r_N s)'`. -/
theorem lift_succ (m c r : Nat) (hr : 3 ≤ r) (s : SignMap) :
    AgreeR (c + 1 + m) (r + 1) (lift (c + 1) s) (expand (lift c s)) := by
  intro Z hZ
  obtain ⟨hlen, hinc, hlt⟩ := hZ
  match Z, hlen, hinc, hlt with
  | z0 :: Z', hlen, hinc, hlt =>
  unfold StrictIncr at hinc
  rw [List.pairwise_cons] at hinc
  simp only [List.length_cons] at hlen
  unfold expand lift
  simp only [List.drop_succ_cons, List.drop_zero, List.length_map, List.length_cons]
  have hpos : ∀ z ∈ Z', 1 ≤ z := fun z hz => by have := hinc.1 z hz; omega
  have hf : ((Z'.map (· - 1)).filter fun x => decide (c ≤ x)).length =
      (Z'.filter fun x => decide (c + 1 ≤ x)).length := by
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro z hz
    have := hpos z hz
    simp only [Function.comp, decide_eq_decide]
    omega
  have htop : ((Z'.map (· - 1)).drop (Z'.length - 3)).map (· - c) =
      ((z0 :: Z').drop (Z'.length + 1 - 3)).map (· - (c + 1)) := by
    have e : Z'.length + 1 - 3 = (Z'.length - 3) + 1 := by omega
    rw [e, List.drop_succ_cons, ← List.map_drop, List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp]
    omega
  rw [hf, htop]
  have hcond : (3 ≤ ((z0 :: Z').filter fun x => decide (c + 1 ≤ x)).length) ↔
      (3 ≤ (Z'.filter fun x => decide (c + 1 ≤ x)).length) := by
    by_cases h0 : c + 1 ≤ z0
    · have hall : (Z'.filter fun x => decide (c + 1 ≤ x)) = Z' :=
        List.filter_eq_self.2 (fun z hz => by have := hinc.1 z hz; simp; omega)
      simp only [List.filter_cons, h0, decide_true, ite_true, List.length_cons, hall]
      omega
    · simp [h0]
  by_cases h3 : 3 ≤ (Z'.filter fun x => decide (c + 1 ≤ x)).length
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hcond.2 h3)), ite_eq_left_of_eq_true _ _ (eq_true h3)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => h3 (hcond.1 h))), ite_eq_right_of_eq_false _ _ (eq_false h3)]

/-- Lemma 8.3(a): the lift of a signotope is a signotope of rank `r = q + 3` (for `c ≥ q`). -/
theorem lift_signotope {m c q : Nat} (hc : q ≤ c) {s : SignMap} (hs : IsSignotopeR m 3 s) :
    IsSignotopeR (c + m) (q + 3) (lift c s) := by
  induction q generalizing c with
  | zero => exact padding_signotope hs
  | succ q ih =>
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have h1 := onestep_a (ih (c := c') (by omega))
    have h2 := lift_succ m c' (q + 3) (by omega) s
    have e1 : c' + m + 1 = c' + 1 + m := by omega
    have e2 : q + 1 + 3 = q + 3 + 1 := by omega
    rw [e1] at h1
    rw [e2]
    exact agreeInv_sig _ _ (fun X hX => (h2 X hX).symm) h1

/-- Lemma 8.3(b): `L s` and `L s^T` differ exactly on the sets `Y ++ (T + c)`, `Y` a `q`-subset of
`[c + min T]`. -/
theorem lift_diff {m c q : Nat} (s : SignMap) {T : List Nat} (hT : IsRSet m 3 T) {X : List Nat}
    (hX : IsRSet (c + m) (q + 3) X) :
    lift c s X ≠ lift c (flipR s T) X ↔ ∃ Y, IsRSet (c + T.headD 0) q Y ∧ X = Y ++ T.map (· + c) := by
  have hTl := hT.1
  unfold lift flipR
  constructor
  · intro hne
    split at hne
    · next hc =>
      have heq : (X.drop (X.length - 3)).map (· - c) = T := by
        apply Classical.byContradiction
        intro hn
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at hne
        exact hne rfl
      have hge := drop_ge_of_filter hX.2.1 hc
      have hdrop : X.drop (X.length - 3) = T.map (· + c) := by
        rw [← heq, List.map_map]
        conv => lhs; rw [← List.map_id (X.drop (X.length - 3))]
        apply List.map_congr_left
        intro x hx
        have := hge x hx
        simp only [Function.comp, id]
        omega
      refine ⟨X.take (X.length - 3), ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.length_take, hX.1]; omega
      · exact hX.2.1.sublist (List.take_sublist _ _)
      · intro y hy
        have hp := hX.2.1
        unfold StrictIncr at hp
        rw [← List.take_append_drop (X.length - 3) X, List.pairwise_append] at hp
        match T, hTl, hdrop with
        | [t0, t1, t2], _, hdrop =>
        have := hp.2.2 y hy (t0 + c) (by rw [hdrop]; simp)
        simp only [List.headD_cons]
        omega
      · conv => lhs; rw [← List.take_append_drop (X.length - 3) X]
        rw [hdrop]
    · exact absurd rfl hne
  · rintro ⟨Y, hY, rfl⟩
    have hYl := hY.1
    have hc : 3 ≤ ((Y ++ T.map (· + c)).filter fun x => decide (c ≤ x)).length := by
      rw [List.filter_append, List.length_append]
      have : ((T.map (· + c)).filter fun x => decide (c ≤ x)) = T.map (· + c) :=
        List.filter_eq_self.2 (fun x hx => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
          simp)
      rw [this, List.length_map]
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have htop : ((Y ++ T.map (· + c)).drop ((Y ++ T.map (· + c)).length - 3)).map (· - c) = T := by
      have e : (Y ++ T.map (· + c)).length - 3 = Y.length := by
        simp [List.length_append]; omega
      rw [e, List.drop_left, List.map_map]
      conv => rhs; rw [← List.map_id T]
      apply List.map_congr_left
      intro x _
      simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true htop)]
    cases s ((Y ++ T.map (· + c)).drop ((Y ++ T.map (· + c)).length - 3) |>.map (· - c)) <;> simp

end OMDistance
