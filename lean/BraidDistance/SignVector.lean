import BraidDistance.Arrangement
import BraidDistance.Signotope

/-!
# Sign vectors of reduced words (Lemma 2.2)

* (order of the three swaps) in a reduced word the swaps of `a < b < c` occur in the order `⟨ab⟩, ⟨ac⟩, ⟨bc⟩`
  or `⟨bc⟩, ⟨ac⟩, ⟨ab⟩` (Definition 2.1): when `⟨ac⟩` is performed, `a` and `c` are adjacent, so `b` lies above
  both or below both, and `arrAfter_order` tells which of `⟨ab⟩`, `⟨bc⟩` already happened;
* (b) the sign vector of a reduced word is a signotope of rank 3;
* (c) a commutation keeps a word reduced and does not change its sign vector.
-/

namespace BraidDistance

/-- A list with an entry at position `i + 1` splits as `L ++ a :: b :: R` with `L` of length `i`. -/
private theorem split_at (arr : List Nat) (i : Nat) (h : i + 1 < arr.length) :
    ∃ L a b R, arr = L ++ a :: b :: R ∧ L.length = i := by
  refine ⟨arr.take i, arr[i], arr[i+1], arr.drop (i+2), ?_, by simp; omega⟩
  conv => lhs; rw [← List.take_append_drop i arr]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]

private theorem nodup_arrAfter (m : Nat) (w : List Nat) : (arrAfter m w).Nodup :=
  (arrFrom_perm (List.range m) w).nodup_iff.mpr List.nodup_range

private theorem mem_arrAfter {m : Nat} (w : List Nat) {b : Nat} (hb : b < m) : b ∈ arrAfter m w :=
  (arrFrom_perm (List.range m) w).mem_iff.mpr (List.mem_range.mpr hb)

/-- Position in `sP ++ q :: T` of a pair occurring once, relative to the position of `q`. -/
private theorem idx_split {sP T : List (Nat × Nat)} {p q : Nat × Nat} (hpq : p ≠ q)
    (hc : (sP ++ q :: T).count p = 1) :
    (sP.count p % 2 = 1 → (sP ++ q :: T).idxOf p < sP.length) ∧
    (sP.count p % 2 = 0 → sP.length < (sP ++ q :: T).idxOf p) := by
  rw [List.count_append] at hc
  rw [List.idxOf_append]
  constructor
  · intro h1
    have hm : p ∈ sP := List.count_pos_iff.mp (by omega)
    simp only [hm, ↓reduceIte]; exact List.idxOf_lt_length_of_mem hm
  · intro h0
    have hm : p ∉ sP := fun hm => by have := List.count_pos_iff.mpr hm; omega
    simp only [hm, ↓reduceIte]; rw [List.idxOf_cons]
    have : (q == p) = false := by simpa using (Ne.symm hpq)
    rw [this]; simp

private theorem swapsFrom_mid (L R C : List Nat) (a b : Nat) :
    swapsFrom (L ++ a :: b :: R) (L.length :: C) = pairOf a b :: swapsFrom (L ++ b :: a :: R) C := by
  simp [swapsFrom, swapAdj]

/-- Two letters at distance at least two swap disjoint pairs of wires, and exchanging the letters exchanges the
two swaps and leaves the rest of the swap list unchanged. -/
private theorem swapsFrom_comm (arr C : List Nat) (i j : Nat) (hij : i + 2 ≤ j)
    (hj : j + 1 < arr.length) (hnd : arr.Nodup) :
    ∃ p q : Nat × Nat, ∃ X, p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p ≠ q ∧
      swapsFrom arr (i :: j :: C) = p :: q :: X ∧ swapsFrom arr (j :: i :: C) = q :: p :: X := by
  obtain ⟨L, a, b, R, rfl, rfl⟩ := split_at arr i (by omega)
  obtain ⟨M, c, d, N, rfl, hM⟩ := split_at R (j - L.length - 2) (by simp at hj; omega)
  have hj' : j = (L ++ a :: b :: M).length := by simp; omega
  have hj'' : j = (L ++ b :: a :: M).length := by simp; omega
  have e1 : L ++ a :: b :: (M ++ c :: d :: N) = (L ++ a :: b :: M) ++ c :: d :: N := by simp
  have e2 : L ++ b :: a :: (M ++ c :: d :: N) = (L ++ b :: a :: M) ++ c :: d :: N := by simp
  have e3 : L ++ a :: b :: (M ++ d :: c :: N) = (L ++ a :: b :: M) ++ d :: c :: N := by simp
  have e4 : L ++ b :: a :: (M ++ d :: c :: N) = (L ++ b :: a :: M) ++ d :: c :: N := by simp
  simp [List.nodup_append, List.nodup_cons] at hnd
  obtain ⟨-, ⟨⟨hab, -, hac, had, -⟩, ⟨-, hbc, hbd, -⟩, -, ⟨⟨hcd, -⟩, -⟩, -⟩, -⟩ := hnd
  refine ⟨pairOf a b, pairOf c d, swapsFrom (L ++ b :: a :: (M ++ d :: c :: N)) C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp only [pairOf, ne_eq, Prod.mk.injEq]; omega)
  · rw [swapsFrom_mid, e2, hj'', swapsFrom_mid, e4]
  · rw [e1, hj', swapsFrom_mid, ← e3, swapsFrom_mid]

/-- Exchanging two adjacent distinct entries `p, q` of a list keeps the relative position of `u` and `v`, unless
`{u, v} = {p, q}`. -/
private theorem idxOf_lt_swap {l₁ X : List (Nat × Nat)} {p q u v : Nat × Nat} (hpq : p ≠ q)
    (h1 : ¬(u = p ∧ v = q)) (h2 : ¬(u = q ∧ v = p)) :
    (l₁ ++ q :: p :: X).idxOf u < (l₁ ++ q :: p :: X).idxOf v ↔
      (l₁ ++ p :: q :: X).idxOf u < (l₁ ++ p :: q :: X).idxOf v := by
  simp only [List.idxOf_append, List.idxOf_cons, beq_iff_eq]
  have hu := fun (hm : u ∈ l₁) => List.idxOf_lt_length_of_mem hm
  have hv := fun (hm : v ∈ l₁) => List.idxOf_lt_length_of_mem hm
  by_cases mu : u ∈ l₁ <;> by_cases mv : v ∈ l₁ <;> simp only [mu, mv, ↓reduceIte] <;>
    first
    | omega
    | (by_cases up : p = u <;> by_cases uq : q = u <;> by_cases vp : p = v <;> by_cases vq : q = v <;>
        simp only [up, uq, vp, vq, ↓reduceIte] <;> first | omega | (subst_vars; first | omega | (simp_all <;> omega)))

/-- The packet of four sign values determined by six swap times, under the triple-order constraints, has at most
one sign change. -/
private theorem packet_arith (ab ac ad bc bd cd : Nat)
    (_h1 : (ab < ac ∧ ac < bc) ∨ (bc < ac ∧ ac < ab))
    (h2 : (ab < ad ∧ ad < bd) ∨ (bd < ad ∧ ad < ab))
    (h3 : (ac < ad ∧ ad < cd) ∨ (cd < ad ∧ ad < ac))
    (h4 : (bc < bd ∧ bd < cd) ∨ (cd < bd ∧ bd < bc)) :
    oneChange [decide (ab < bc), decide (ab < bd), decide (ac < cd), decide (bc < cd)] = true := by
  by_cases p1 : ab < bc <;> by_cases p2 : ab < bd <;> by_cases p3 : ac < cd <;> by_cases p4 : bc < cd <;>
    simp [oneChange, signChanges, p1, p2, p3, p4] <;> omega

/-- The two possible orders of the three swaps of a triple (Definition 2.1). -/
theorem Reduced.triple_order {m : Nat} {w : List Nat} (h : Reduced m w) {a b c : Nat}
    (hab : a < b) (hbc : b < c) (hc : c < m) :
    ((swaps m w).idxOf (a, b) < (swaps m w).idxOf (a, c) ∧
      (swaps m w).idxOf (a, c) < (swaps m w).idxOf (b, c)) ∨
    ((swaps m w).idxOf (b, c) < (swaps m w).idxOf (a, c) ∧
      (swaps m w).idxOf (a, c) < (swaps m w).idxOf (a, b)) := by
  obtain ⟨hv, hc1⟩ := h
  have hcac := hc1 c hc a (by omega)
  have hcab := hc1 b (by omega) a hab
  have hcbc := hc1 c hc b hbc
  have hac : (a, c) ∈ swaps m w := List.count_pos_iff.mp (by omega)
  obtain ⟨j, hjdef⟩ : ∃ j, (swaps m w).idxOf (a, c) = j := ⟨_, rfl⟩
  have hj : j < w.length := by
    rw [← hjdef, ← swapsFrom_length (List.range m) w]; exact List.idxOf_lt_length_of_mem hac
  obtain ⟨P, x, R, hw, hPl⟩ : ∃ P x R, w = P ++ x :: R ∧ P.length = j :=
    ⟨w.take j, w[j], w.drop (j+1), by rw [← List.drop_eq_getElem_cons hj]; simp, by simp; omega⟩
  subst hw
  have hvP : ValidWord m P := fun i hi => hv i (List.mem_append_left _ hi)
  have hx : x + 1 < m := hv x (by simp)
  have hS : swaps m (P ++ x :: R) = swaps m P ++ swapsFrom (arrAfter m P) (x :: R) :=
    swapsFrom_append _ _ _
  have hsPl : (swaps m P).length = j := by rw [← hPl]; exact swapsFrom_length _ _
  obtain ⟨L, y, z, M, harr, hLl⟩ := split_at (arrAfter m P) x (by rw [arrAfter_length]; omega)
  subst hLl
  have hnd := nodup_arrAfter m P
  have hbm := mem_arrAfter P (show b < m by omega)
  rw [harr] at hnd hbm
  have hsf : swapsFrom (arrAfter m P) (L.length :: R) =
      pairOf y z :: swapsFrom (swapAdj (arrAfter m P) L.length) R := by
    simp only [swapsFrom]; rw [harr]; simp
  rw [hS, hsf] at hjdef hcac hcab hcbc ⊢
  -- the pair at position `j` is `(a, c)`
  have hpyz : pairOf y z = (a, c) := by
    rw [List.idxOf_append] at hjdef
    split at hjdef
    · rename_i hm; have := List.idxOf_lt_length_of_mem hm; omega
    · rw [List.idxOf_cons] at hjdef
      split at hjdef
      · rename_i he; exact eq_of_beq he
      · omega
  generalize swapsFrom (swapAdj (arrAfter m P) L.length) R = T at hjdef hcac hcab hcbc ⊢
  rw [hpyz] at hjdef hcab hcbc ⊢
  have hyz : (y = a ∧ z = c) ∨ (y = c ∧ z = a) := by
    simp only [pairOf, Prod.mk.injEq] at hpyz; omega
  -- positions in the arrangement
  have hnd' := List.nodup_append.mp hnd
  have hyL : y ∉ L := fun hm => by have := hnd'.2.2 y hm y (by simp); simp at this
  have hzL : z ∉ L := fun hm => by have := hnd'.2.2 z hm z (by simp); simp at this
  have hyz' : y ≠ z := by
    have := hnd'.2.1; simp at this; exact this.1.1
  have hbne : b ≠ y ∧ b ≠ z := by omega
  have ipy : (L ++ y :: z :: M).idxOf y = L.length := by simp [List.idxOf_append, hyL]
  have ipz : (L ++ y :: z :: M).idxOf z = L.length + 1 := by
    have : (y == z) = false := by simpa using hyz'
    rw [List.idxOf_append]; simp only [hzL, ↓reduceIte]; rw [List.idxOf_cons, this]; simp; omega
  have ipb : (L ++ y :: z :: M).idxOf b < L.length ∨ L.length + 1 < (L ++ y :: z :: M).idxOf b := by
    rw [List.idxOf_append]
    split
    · rename_i hm; left; exact List.idxOf_lt_length_of_mem hm
    · right; simp [List.idxOf_cons, Ne.symm hbne.1, Ne.symm hbne.2]; omega
  have o1 := arrAfter_order hvP hab (by omega)
  have o2 := arrAfter_order hvP hbc hc
  rw [harr] at o1 o2
  have i1 := idx_split (show (a, b) ≠ (a, c) by simp; omega) hcab
  have i2 := idx_split (show (b, c) ≠ (a, c) by simp; omega) hcbc
  rw [hsPl] at i1 i2
  have p1 := Nat.mod_two_eq_zero_or_one ((swaps m P).count (a, b))
  have p2 := Nat.mod_two_eq_zero_or_one ((swaps m P).count (b, c))
  have key : ((L ++ y :: z :: M).idxOf a = L.length ∧ (L ++ y :: z :: M).idxOf c = L.length + 1) ∨
      ((L ++ y :: z :: M).idxOf a = L.length + 1 ∧ (L ++ y :: z :: M).idxOf c = L.length) := by
    rcases hyz with ⟨hy, hz⟩ | ⟨hy, hz⟩
    · left; rw [← hy, ← hz]; exact ⟨ipy, ipz⟩
    · right; rw [← hy, ← hz]; exact ⟨ipz, ipy⟩
  clear ipy ipz hyz hbne
  rcases key with ⟨ka, kc⟩ | ⟨ka, kc⟩ <;> rcases ipb with hb | hb
  · -- b above a and c
    have e1 : (swaps m P).count (a, b) % 2 = 1 := by
      rcases p1 with p1 | p1
      · have := o1.mpr p1; omega
      · exact p1
    have e2 : (swaps m P).count (b, c) % 2 = 0 := o2.mp (by omega)
    left; exact ⟨by have := i1.1 e1; omega, by have := i2.2 e2; omega⟩
  · have e1 : (swaps m P).count (a, b) % 2 = 0 := o1.mp (by omega)
    have e2 : (swaps m P).count (b, c) % 2 = 1 := by
      rcases p2 with p2 | p2
      · have := o2.mpr p2; omega
      · exact p2
    right; exact ⟨by have := i2.1 e2; omega, by have := i1.2 e1; omega⟩
  · have e1 : (swaps m P).count (a, b) % 2 = 1 := by
      rcases p1 with p1 | p1
      · have := o1.mpr p1; omega
      · exact p1
    have e2 : (swaps m P).count (b, c) % 2 = 0 := o2.mp (by omega)
    left; exact ⟨by have := i1.1 e1; omega, by have := i2.2 e2; omega⟩
  · have e1 : (swaps m P).count (a, b) % 2 = 0 := o1.mp (by omega)
    have e2 : (swaps m P).count (b, c) % 2 = 1 := by
      rcases p2 with p2 | p2
      · have := o2.mpr p2; omega
      · exact p2
    right; exact ⟨by have := i2.1 e2; omega, by have := i1.2 e1; omega⟩

/-- Lemma 2.2(b): the sign vector of a reduced word is a signotope of rank 3. -/
theorem Reduced.signotope {m : Nat} {w : List Nat} (h : Reduced m w) : IsSignotope m (signVec m w) := by
  intro d hd c hc b hb a ha
  exact packet_arith _ _ _ _ _ _ (h.triple_order ha hb (by omega)) (h.triple_order ha (by omega) hd)
    (h.triple_order (by omega) hc hd) (h.triple_order hb hc hd)

/-- Lemma 2.2(c): a commutation keeps a reduced word reduced and does not change its sign vector. -/
theorem Step.comm_reduced {m : Nat} {w w' : List Nat} (h : Reduced m w) (hs : Step w w' 0) :
    Reduced m w' ∧ signVec m w' = signVec m w := by
  cases hs with
  | comm A C i j hij =>
    obtain ⟨hv, hc⟩ := h
    have hi : i + 1 < m := hv i (by simp)
    have hj : j + 1 < m := hv j (by simp)
    have hnd := nodup_arrAfter m A
    have hlen := arrAfter_length m A
    obtain ⟨p, q, X, d1, d2, d3, d4, hpq, e1, e2⟩ : ∃ p q : Nat × Nat, ∃ X,
        p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 ∧ p ≠ q ∧
        swapsFrom (arrAfter m A) (i :: j :: C) = p :: q :: X ∧
        swapsFrom (arrAfter m A) (j :: i :: C) = q :: p :: X := by
      rcases hij with hij | hij
      · exact swapsFrom_comm _ _ _ _ hij (by omega) hnd
      · obtain ⟨p, q, X, d1, d2, d3, d4, hpq, e1, e2⟩ := swapsFrom_comm (arrAfter m A) C _ _ hij (by omega) hnd
        exact ⟨q, p, X, Ne.symm d1, Ne.symm d3, Ne.symm d2, Ne.symm d4, Ne.symm hpq, e2, e1⟩
    have hS : swaps m (A ++ i :: j :: C) = swaps m A ++ p :: q :: X := by
      rw [← e1]; exact swapsFrom_append _ _ _
    have hS' : swaps m (A ++ j :: i :: C) = swaps m A ++ q :: p :: X := by
      rw [← e2]; exact swapsFrom_append _ _ _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k hk
      apply hv
      simp only [List.mem_append, List.mem_cons] at hk ⊢
      rcases hk with h | h | h | h <;> simp [h]
    · intro b hb a ha
      have := hc b hb a ha
      rw [hS] at this
      rw [hS']
      simp only [List.count_append, List.count_cons, beq_iff_eq] at this ⊢
      omega
    · funext a b c
      simp only [signVec, hS, hS', decide_eq_decide]
      refine idxOf_lt_swap hpq ?_ ?_
      · rintro ⟨rfl, rfl⟩; exact d3 rfl
      · rintro ⟨rfl, rfl⟩; exact d2 rfl

end BraidDistance
