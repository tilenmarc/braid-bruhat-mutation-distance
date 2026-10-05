import OMDistance.LiftFlip
import OMDistance.LiftHamming

/-!
# Proposition 8.5, the upper bound

For a walk of length `k` in `B(S, 2)` from `s` to `t` there is a walk in `B(N ∪ S, r-1)` from `L s` to `L t` of
length `ℓ` with `ℓ - H ≤ μ (k - h)`, i.e. `ℓ + μ h ≤ H + μ k`, where `h = |D(s,t)|`, `H = |D(L s, L t)|` and
`μ = binom(c + m - 3, q)`.

Proof: replace each step flipping `T` by the walk of Lemma 8.4 (`liftflip`), of length
`μ_T = binom(c + min T, q) ≤ μ`.  The length is `Σ_T μ_T n_T = H + Σ_T μ_T (n_T - [T ∈ D(s,t)]) ≤ H + μ (k - h)`.
Equivalently, by induction on the walk: if the first step flips `T`, then `h` and `H` change by `∓1` and `∓μ_T`
according to whether `T ∈ D(s, t)` (Lemma 8.3(b)), and `μ_T ≤ μ`.
-/

namespace OMDistance

/-- Summing `f` over a filter is summing `f` masked by the predicate. -/
private theorem sum_map_filter {α : Type} (L : List α) (p : α → Bool) (f : α → Nat) :
    ((L.filter p).map f).sum = (L.map fun x => if p x then f x else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : p a <;> simp [h, ih]

private theorem sum_map_congr {α : Type} (L : List α) (g g' : α → Nat) (h : ∀ Y ∈ L, g Y = g' Y) :
    (L.map g).sum = (L.map g').sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih (fun Y hY => h Y (by simp [hY]))]

/-- Two summands that agree away from one element `X` of a duplicate-free list. -/
private theorem sum_map_swap {α : Type} [DecidableEq α] (L : List α) (g g' : α → Nat) (X : α) (hnd : L.Nodup)
    (hX : X ∈ L) (h : ∀ Y ∈ L, Y ≠ X → g Y = g' Y) :
    (L.map g).sum + g' X = (L.map g').sum + g X := by
  induction L with
  | nil => simp at hX
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hnd' : L.Nodup := (List.nodup_cons.1 hnd).2
    by_cases haX : a = X
    · subst haX
      have hnot : a ∉ L := (List.nodup_cons.1 hnd).1
      have e := sum_map_congr L g g' (fun Y hY => h Y (by simp [hY]) (fun hh => hnot (hh ▸ hY)))
      rw [e]
      omega
    · have hX' : X ∈ L := by
        simp only [List.mem_cons] at hX
        rcases hX with hX | hX
        · exact absurd hX.symm haX
        · exact hX
      have e := ih hnd' hX' (fun Y hY hYX => h Y (by simp [hY]) hYX)
      rw [h a (by simp) haX]
      omega

/-- How a weighted Hamming distance changes along one flip. -/
private theorem diff_sum_flip {M r : Nat} {u v w : SignMap} {X : List Nat} (hX : IsRSet M r X)
    (hv : AgreeR M r (flipR u X) v) (f : List Nat → Nat) :
    ((diffR M r v w).map f).sum + (if u X != w X then f X else 0) =
      ((diffR M r u w).map f).sum + (if v X != w X then f X else 0) := by
  unfold diffR
  rw [sum_map_filter, sum_map_filter]
  refine sum_map_swap (rsets M r) (fun Y => if (v Y != w Y) = true then f Y else 0)
    (fun Y => if (u Y != w Y) = true then f Y else 0) X (rsets_nodup M r) (mem_rsets.2 hX) ?_
  intro Y hY hYX
  rw [← hv Y (mem_rsets.1 hY), flipR_ne u hYX]

private theorem sum_map_one {α : Type} (L : List α) : (L.map fun _ => (1 : Nat)).sum = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

/-- Being a signotope depends only on the values on the `r`-subsets. -/
private theorem sigAgreeInv (M r : Nat) : AgreeInv M r (IsSignotopeR M r) := by
  intro u u' hag hu P hP
  have e : rpacket u P = rpacket u' P := by
    unfold rpacket
    apply List.map_congr_left
    intro i hi
    rw [List.mem_reverse, List.mem_range, hP.1] at hi
    exact hag _ (hP.eraseIdx hi)
  rw [← e]
  exact hu P hP

private theorem headD_le {m : Nat} {T : List Nat} (hT : IsRSet m 3 T) : T.headD 0 + 3 ≤ m := by
  obtain ⟨hlen, hinc, hlt⟩ := hT
  match T, hlen, hinc with
  | [a, b, d], _, hinc =>
    simp only [BraidDistance.StrictIncr, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq] at hinc
    have := hlt d (by simp)
    simp only [List.headD]
    omega

/-- Proposition 8.5, upper bound. -/
theorem excess_upper {m c q : Nat} (hc : q ≤ c) {s t : SignMap} {k : Nat} (hw : SigWalk m 3 s t k) :
    ∃ ℓ, SigWalk (c + m) (q + 3) (lift c s) (lift c t) ℓ ∧
      ℓ + binom (c + m - 3) q * hamR m 3 s t ≤
        hamR (c + m) (q + 3) (lift c s) (lift c t) + binom (c + m - 3) q * k := by
  induction hw with
  | @nil a b hs hst =>
    refine ⟨0, RWalk.nil (lift_signotope hc hs) (lift_congr hst), ?_⟩
    have h0 : hamR m 3 a b = 0 := by
      have e : hamR m 3 a b = hamR m 3 a a := hamR_congr (AgreeR.refl m 3 a) hst.symm
      rw [e]
      unfold hamR diffR
      simp
    rw [h0]
    omega
  | @cons u v w k hu hd hvw ih =>
    obtain ⟨ℓ, hwl, hle⟩ := ih
    obtain ⟨T, hT, hag⟩ := differsInOneR_iff.1 hd
    have hv : IsSignotopeR m 3 v := hvw.start
    have huT : IsSignotopeR m 3 (flipR u T) := sigAgreeInv m 3 _ _ hag.symm hv
    have hstep := liftflip hc hT hu huT
    have hwl' : SigWalk (c + m) (q + 3) (lift c (flipR u T)) (lift c w) ℓ :=
      hwl.congr_start (sigAgreeInv _ _) (lift_congr hag.symm)
    refine ⟨binom (c + T.headD 0) q + ℓ, hstep.append (sigAgreeInv _ _) hwl', ?_⟩
    have hμ : binom (c + T.headD 0) q ≤ binom (c + m - 3) q := by
      apply binom_mono
      have := headD_le hT
      omega
    -- the two changes
    have eh := diff_sum_flip (w := w) hT hag (fun _ => 1)
    have eH := diff_sum_flip (w := w) hT hag (fun T => binom (c + T.headD 0) q)
    rw [sum_map_one, sum_map_one] at eh
    rw [← hamR_lift, ← hamR_lift] at eH
    change hamR m 3 v w + _ = hamR m 3 u w + _ at eh
    have hvT : v T = !u T := by rw [← hag T hT, flipR_self]
    rw [hvT] at eh eH
    generalize binom (c + m - 3) q = μ at hle hμ ⊢
    generalize binom (c + T.headD 0) q = μT at eH hμ ⊢
    rw [Nat.mul_succ]
    by_cases hne : u T = w T
    · simp [hne] at eh eH
      have e1 : μ * hamR m 3 v w = μ * hamR m 3 u w + μ := by rw [eh, Nat.mul_succ]
      omega
    · have hne' : (!u T) = w T := by
        cases h1 : u T <;> cases h2 : w T <;> simp_all
      simp [hne, hne'] at eh eH
      have e1 : μ * hamR m 3 u w = μ * hamR m 3 v w + μ := by rw [← eh, Nat.mul_succ]
      omega

end OMDistance
