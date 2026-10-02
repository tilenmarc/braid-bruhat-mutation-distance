import BraidDistance.BasicLemmas

/-!
# Walks as flip lists, the Hamming bound and parity (Lemma 2.5)

* A walk of signotopes of length `k` from `s` to `v` is the same as a list of `k` flipped valid triples from `s`
  whose prefixes all give signotopes, ending at a map agreeing with `v` (`walk_to_flips`).
* Lemma 2.5: a triple of `D = D(s, v)` is flipped an odd number of times and any other valid triple an even
  number of times; so if `Ys` is a duplicate-free list of triples each flipped more often than necessary
  (`count > [t ∈ D]`), the walk has length at least `|D| + 2 |Ys|`.
* Hamming distances add up along a chain of maps in which every triple changes at most once (used for
  Corollary 4.6(b)).
-/

namespace BraidDistance

/-- Flipping the unique differing triple of an edge `u — v` gives a map agreeing with `v`. -/
private theorem agree_flipT_of_differsInOne {m : Nat} {u v : SMap} {t : Triple} (ht : ValidTriple m t)
    (hne : u.at t ≠ v.at t) (hrest : ∀ t' : Triple, ValidTriple m t' → t' ≠ t → u.at t' = v.at t') :
    Agree m (flipT u t) v := by
  intro a b c h1 h2 h3
  by_cases h : (a, b, c) = t
  · subst h
    simp only [flipT, ite_true]
    simp only [SMap.at] at hne
    cases hu : u a b c <;> cases hv : v a b c <;> simp_all
  · simp only [flipT, h, ite_false]
    exact hrest (a, b, c) ⟨h1, h2, h3⟩ h

/-- A walk of signotopes gives its list of flipped triples. -/
theorem walk_to_flips {m : Nat} {s v : SMap} {k : Nat} (hw : Walk m s v k) :
    ∃ ts : List Triple, ts.length = k ∧ FlipWalk m s ts ∧ Agree m (flipList s ts) v := by
  induction hw with
  | nil hu hag =>
    refine ⟨[], rfl, ⟨by simp, fun i _ => by simpa [flipList] using hu⟩, by simpa [flipList] using hag⟩
  | @cons u v w k hu hd _ ih =>
    obtain ⟨ts, hlen, ⟨hval, hsig⟩, hend⟩ := ih
    obtain ⟨t, ht, hne, hrest⟩ := hd
    have hag := agree_flipT_of_differsInOne ht hne hrest
    refine ⟨t :: ts, by simp [hlen], ⟨?_, ?_⟩, ?_⟩
    · intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | h
      · exact ht
      · exact hval t' h
    · intro i hi
      cases i with
      | zero => simpa [flipList] using hu
      | succ i =>
        have e : flipList u ((t :: ts).take (i + 1)) = flipList (flipT u t) (ts.take i) := rfl
        rw [e]
        exact IsSignotope.congr (flipList_congr hag.symm _)
          (hsig i (by simp at hi; omega))
    · have e : flipList u (t :: ts) = flipList (flipT u t) ts := rfl
      rw [e]
      exact (flipList_congr hag ts).trans hend

/-- Parity: the number of flips of a valid triple is odd iff the triple lies in `D`. -/
theorem count_parity {m : Nat} {s v : SMap} {ts : List Triple}
    (hend : Agree m (flipList s ts) v) {t : Triple} (ht : ValidTriple m t) :
    ts.count t % 2 = if t ∈ diffList m s v then 1 else 0 := by
  have e1 := flipList_at s ts t
  rw [Agree.at hend ht] at e1
  have hmod : ts.count t % 2 = 0 ∨ ts.count t % 2 = 1 := by omega
  by_cases hd : t ∈ diffList m s v
  · simp only [hd, ↓reduceIte]
    have hne := (mem_diffList.1 hd).2
    rcases hmod with h | h
    · rw [h] at e1
      exact absurd (by simpa using e1.symm) hne
    · exact h
  · simp only [hd, ↓reduceIte]
    have heq : s.at t = v.at t := by
      by_cases hne : s.at t = v.at t
      · exact hne
      · exact absurd (mem_diffList.2 ⟨ht, hne⟩) hd
    rcases hmod with h | h
    · exact h
    · rw [h, heq] at e1
      cases hv : v.at t <;> simp [hv] at e1

private theorem sum_count_cons (x : Triple) (ts L : List Triple) :
    (L.map fun t => (x :: ts).count t).sum = (L.map fun t => ts.count t).sum + L.count x := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, @List.count_cons _ _ y x ts, @List.count_cons _ _ x y L]
    by_cases h : x = y
    · subst h; simp; omega
    · have h1 : (x == y) = false := by simpa using h
      have h2 : (y == x) = false := by simpa using Ne.symm h
      simp [h1, h2]; omega

private theorem count_le_one_of_nodup (x : Triple) (L : List Triple) (hL : L.Nodup) : L.count x ≤ 1 := by
  induction L with
  | nil => simp
  | cons y L ih =>
    have hL' := List.nodup_cons.1 hL
    rw [List.count_cons]
    by_cases h : y = x
    · subst h
      have : L.count y = 0 := List.count_eq_zero.2 hL'.1
      simp [this]
    · have : (y == x) = false := by simpa using h
      simp only [this]
      have := ih hL'.2
      simp; omega

/-- The counts of distinct triples add up to at most the length of the list. -/
theorem sum_count_le (ts L : List Triple) (hL : L.Nodup) :
    (L.map fun t => ts.count t).sum ≤ ts.length := by
  induction ts with
  | nil => induction L with
    | nil => simp
    | cons y L ih => simp at ih ⊢; exact ih (List.nodup_cons.1 hL).2
  | cons x ts ih =>
    rw [sum_count_cons]
    have := count_le_one_of_nodup x L hL
    simp only [List.length_cons]
    omega

private theorem sum_map_le_sum_map {L : List Triple} {f g : Triple → Nat} (h : ∀ t ∈ L, g t ≤ f t) :
    (L.map g).sum ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h y (List.mem_cons_self ..)
    have h2 := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    omega

private theorem sum_map_add {L : List Triple} {f g : Triple → Nat} :
    (L.map fun t => f t + g t).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons y L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_ind (L : List Triple) (p : Triple → Bool) :
    (L.map fun t => if p t then 1 else 0).sum = (L.filter p).length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases p y <;> simp; omega

private theorem sum_map_const (L : List Triple) (c : Nat) :
    (L.map fun _ => c).sum = c * L.length := by
  induction L with
  | nil => simp
  | cons y L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; rw [Nat.mul_succ]; omega

private theorem length_filter_split (L : List Triple) (p : Triple → Bool) :
    L.length = (L.filter p).length + (L.filter fun t => !p t).length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.filter_cons, List.length_cons]
    cases p y <;> simp <;> omega

private theorem nodup_filter {L : List Triple} (p : Triple → Bool) (h : L.Nodup) : (L.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at h ⊢
  exact h.filter _

private theorem parity_bound_aux (D : List Triple) (hDn : D.Nodup) (ts Ys : List Triple)
    (hY : Ys.Nodup)
    (hpY : ∀ t ∈ Ys, ts.count t % 2 = (if t ∈ D then 1 else 0))
    (hpD : ∀ t ∈ D, ts.count t % 2 = 1)
    (hYc : ∀ t ∈ Ys, (if t ∈ D then 1 else 0) < ts.count t) :
    D.length + 2 * Ys.length ≤ ts.length := by
  -- the list `Ys ++ (D \ Ys)` is duplicate-free
  have hLn : (Ys ++ D.filter fun t => !decide (t ∈ Ys)).Nodup := by
    rw [List.nodup_append]
    refine ⟨hY, nodup_filter _ hDn, ?_⟩
    intro a ha b hb hab
    subst hab
    have := (List.mem_filter.1 hb).2
    simp [ha] at this
  have hsum := sum_count_le ts _ hLn
  rw [List.map_append, List.sum_append] at hsum
  -- bound on `Ys`
  have hY1 : ∀ t ∈ Ys, (fun t => (if decide (t ∈ D) then 1 else 0) + 2) t ≤ ts.count t := by
    intro t ht
    have hp := hpY t ht
    have hc := hYc t ht
    by_cases hd : t ∈ D
    · simp only [hd, ite_true, decide_true] at hp hc ⊢
      omega
    · simp only [hd, ite_false, decide_false, Bool.false_eq_true] at hp hc ⊢
      omega
  have hS1 := sum_map_le_sum_map hY1
  rw [sum_map_add, sum_map_ind, sum_map_const] at hS1
  -- bound on `D \ Ys`
  have hD1 : ∀ t ∈ D.filter (fun t => !decide (t ∈ Ys)), (fun _ => 1) t ≤ ts.count t := by
    intro t ht
    have hp := hpD t (List.mem_filter.1 ht).1
    simp only; omega
  have hS2 := sum_map_le_sum_map hD1
  rw [sum_map_const] at hS2
  -- `|D ∩ Ys| ≤ |Ys ∩ D|`
  have hcap := sum_count_le (Ys.filter fun t => decide (t ∈ D)) (D.filter fun t => decide (t ∈ Ys))
    (nodup_filter _ hDn)
  have hD3 : ∀ t ∈ D.filter (fun t => decide (t ∈ Ys)),
      (fun _ => 1) t ≤ (Ys.filter fun t => decide (t ∈ D)).count t := by
    intro t ht
    have h := List.mem_filter.1 ht
    have hm : t ∈ Ys.filter (fun t => decide (t ∈ D)) :=
      List.mem_filter.2 ⟨by simpa using h.2, by simpa using h.1⟩
    exact List.count_pos_iff.2 hm
  have hS3 := sum_map_le_sum_map hD3
  rw [sum_map_const] at hS3
  have hsplit := length_filter_split D (fun t => decide (t ∈ Ys))
  omega

/-- Lemma 2.5: `|D| + 2|Y| ≤ ∑ c_X` for a list `Ys` of triples flipped more often than necessary. -/
theorem parity_bound {m : Nat} {s v : SMap} {ts : List Triple}
    (_hv : ∀ t ∈ ts, ValidTriple m t) (hend : Agree m (flipList s ts) v)
    (Ys : List Triple) (hY : Ys.Nodup) (hYv : ∀ t ∈ Ys, ValidTriple m t)
    (hYc : ∀ t ∈ Ys, (if t ∈ diffList m s v then 1 else 0) < ts.count t) :
    hamming m s v + 2 * Ys.length ≤ ts.length := by
  refine parity_bound_aux (diffList m s v) (diffList_nodup m s v) ts Ys hY
    (fun t ht => count_parity hend (hYv t ht)) (fun t ht => ?_) hYc
  have h := count_parity hend (mem_diffList.1 ht).1
  simp only [ht, ↓reduceIte] at h
  exact h

private theorem exists_change (us : Nat → SMap) (t : Triple) :
    ∀ J, (us 0).at t ≠ (us J).at t → ∃ k < J, (us k).at t ≠ (us (k + 1)).at t := by
  intro J
  induction J with
  | zero => intro h; exact absurd rfl h
  | succ J ih =>
    intro h
    by_cases hJ : (us J).at t = (us (J + 1)).at t
    · rw [← hJ] at h
      obtain ⟨k, hk, hk'⟩ := ih h
      exact ⟨k, by omega, hk'⟩
    · exact ⟨J, by omega, hJ⟩

private theorem length_filter_or (l : List Triple) (q r : Triple → Bool)
    (h : ∀ t ∈ l, ¬ (q t = true ∧ r t = true)) :
    (l.filter fun t => q t || r t).length = (l.filter q).length + (l.filter r).length := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have ih' := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hy := h y (List.mem_cons_self ..)
    simp only [List.filter_cons]
    cases hq : q y <;> cases hr : r y <;> simp_all <;> omega

/-- Hamming distances add up along a chain in which every valid triple changes at most once. -/
theorem hamming_chain (m J : Nat) (us : Nat → SMap)
    (h : ∀ t : Triple, ValidTriple m t →
      ((List.range J).filter fun k => (us k).at t != (us (k + 1)).at t).length ≤ 1) :
    hamming m (us 0) (us J) = ((List.range J).map fun k => hamming m (us k) (us (k + 1))).sum := by
  induction J with
  | zero => simp [hamming, diffList]
  | succ J ih =>
    have hsplit : ∀ t : Triple,
        ((List.range (J + 1)).filter fun k => (us k).at t != (us (k + 1)).at t).length =
        ((List.range J).filter fun k => (us k).at t != (us (k + 1)).at t).length +
        (if (us J).at t != (us (J + 1)).at t then 1 else 0) := by
      intro t
      rw [List.range_succ, List.filter_append, List.length_append]
      simp only [List.filter_cons, List.filter_nil]
      split <;> simp_all
    have ih' := ih fun t ht => by have := h t ht; rw [hsplit] at this; omega
    rw [List.range_succ, List.map_append, List.sum_append, ← ih']
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    unfold hamming diffList
    rw [← length_filter_or]
    · congr 1
      apply List.filter_congr
      intro t ht
      have hv := mem_triples.1 ht
      have h1 := h t hv
      rw [hsplit] at h1
      by_cases hc1 : (us J).at t = (us (J + 1)).at t
      · rw [hc1]; simp
      · have hc0 : (us 0).at t = (us J).at t := by
          refine Decidable.byContradiction fun hc0 => ?_
          obtain ⟨k, hk, hk'⟩ := exists_change us t J hc0
          have hm : k ∈ (List.range J).filter fun k => (us k).at t != (us (k + 1)).at t :=
            List.mem_filter.2 ⟨List.mem_range.2 hk, by simpa using hk'⟩
          have := List.length_pos_of_mem hm
          have hi : ((us J).at t != (us (J + 1)).at t) = true := by simpa using hc1
          simp only [hi, ↓reduceIte] at h1
          omega
        rw [hc0]; simp
    · intro t ht ⟨hq, hr⟩
      have hv := mem_triples.1 ht
      have h1 := h t hv
      rw [hsplit] at h1; simp only [hr, ↓reduceIte] at h1
      have hc0 : (us 0).at t ≠ (us J).at t := by simpa using hq
      obtain ⟨k, hk, hk'⟩ := exists_change us t J hc0
      have hm : k ∈ (List.range J).filter fun k => (us k).at t != (us (k + 1)).at t :=
        List.mem_filter.2 ⟨List.mem_range.2 hk, by simpa using hk'⟩
      have := List.length_pos_of_mem hm
      omega

end BraidDistance
