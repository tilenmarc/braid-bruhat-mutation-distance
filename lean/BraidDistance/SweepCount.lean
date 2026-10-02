import BraidDistance.SweepPairs

/-!
# Counting the factors (Corollary 4.6(b), the arithmetic)

`Φ̂` has `|E|` cells, `C(n,2) - |E|` factors of kind (XX), `(n-2)|E|` of kinds (Xp)/(pX), and otherwise (pp)
factors, so the sum of the `|D_k|` is `30|E| + 18(C(n,2) - |E|) + 3(n-2)|E| = 3n(m-3) + 6|E|`.
-/

namespace BraidDistance

namespace SweepCountAux

private theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → Nat) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]; omega

private theorem sum_map_mul {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]

private theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map fun _ => c).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_add]; omega

private theorem sum_map_zero {α : Type} (l : List α) (f : α → Nat) (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

private theorem sum_map_congr {α : Type} {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

private theorem length_filter_eq {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a <;> simp [hp, ih] <;> omega

private theorem sum_ite_eq (l : List Nat) (a : Nat) :
    (l.map fun x => if x = a then 1 else 0).sum = l.count a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a <;> simp [h, ih] <;> omega

private theorem len_split (l : List Nat) (w : Nat) :
    (l.filter (fun x => decide (x < w))).length + (l.filter (fun x => decide (w < x))).length
      + l.count w = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, List.count_cons, List.length_cons]
    by_cases h1 : a < w
    · have : ¬ w < a := by omega
      have : ¬ (a == w) = true := by simp; omega
      simp [*]; omega
    · by_cases h2 : w < a
      · have : ¬ (a == w) = true := by simp; omega
        simp [*]; omega
      · have : a = w := by omega
        subst this
        simp [h1]; omega

private theorem len_le (l : List Nat) (w : Nat) :
    (l.filter (fun x => decide (w ≤ x))).length
      = (l.filter (fun x => decide (w < x))).length + l.count w := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, List.count_cons]
    by_cases h2 : w < a
    · have : ¬ (a == w) = true := by simp; omega
      have : w ≤ a := by omega
      simp [*]; omega
    · by_cases h1 : a = w
      · subst h1; simp [h2]; omega
      · have : ¬ w ≤ a := by omega
        simp [h2, h1, this, ih]

private theorem count_up (G : Graph) (u w : Nat) (huw : u < w) (hw : w < G.n) :
    (G.up u).count w = if G.isEdge u w then 1 else 0 := by
  unfold Graph.up
  rw [List.Nodup.count (List.Pairwise.filter _ List.nodup_range)]
  by_cases h : G.isEdge u w <;> simp [h, huw, hw]


@[simp] private theorem evHam_pp (a b c d : Nat) : evHam (.mv (.p a b) (.p c d)) = 0 := rfl
@[simp] private theorem evHam_pX (a b c : Nat) : evHam (.mv (.p a b) (.X c)) = 3 := rfl
@[simp] private theorem evHam_Xp (a c d : Nat) : evHam (.mv (.X a) (.p c d)) = 3 := rfl
@[simp] private theorem evHam_XX (a c : Nat) : evHam (.mv (.X a) (.X c)) = 18 := rfl
@[simp] private theorem evHam_cell (a c : Nat) : evHam (.cell a c) = 30 := rfl

private theorem pass_sum (G : Graph) (u w : Nat) (huw : u < w) (hw : w < G.n) :
    ((passEvents G u w).map evHam).sum
      = 3 * (G.up u).length + 3 * (G.up w).length + 18 + 9 * (if G.isEdge u w then 1 else 0) := by
  have hs := len_split (G.up u) w
  have hc := count_up G u w huw hw
  unfold passEvents
  split
  · rename_i he
    simp [Function.comp_def, sum_map_flatMap, sum_map_const, List.map_reverse, List.sum_reverse]
    simp [he] at hc; omega
  · rename_i he
    have hl := len_le (G.up u) w
    simp [Function.comp_def, sum_map_flatMap, sum_map_const, List.map_reverse, List.sum_reverse]
    simp [he] at hc; omega


private theorem completion_sum (G : Graph) (u : Nat) : ((completionEvents G u).map evHam).sum = 0 := by
  unfold completionEvents
  rw [sum_map_flatMap]
  apply sum_map_zero
  intro j hj
  have hj' : j < (List.map (Grp.p u) (G.up u)).length := by simpa using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, List.getElem_map]
  apply sum_map_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  rw [← List.map_take] at he
  simp only [List.mem_map] at he
  obtain ⟨g, -, rfl⟩ := he
  simp

private theorem range'_sum (n u : Nat) (hu : u < n) (P : Nat → Nat) :
    ((List.range' (u + 1) (n - (u + 1))).map P).sum
      = ((List.range n).map fun w => if u < w then P w else 0).sum := by
  have : List.range n = List.range' 0 (u + 1) ++ List.range' (u + 1) (n - (u + 1)) := by
    have h := @List.range'_append 0 (u + 1) (n - (u + 1)) 1
    simp only [Nat.zero_add, Nat.one_mul] at h
    rw [List.range_eq_range', h]
    congr 1; omega
  rw [this, List.map_append, List.sum_append]
  rw [sum_map_zero (List.range' 0 (u + 1)) _ (by
    intro x hx; simp [List.mem_range'] at hx; simp; omega)]
  rw [Nat.zero_add]
  apply sum_map_congr
  intro x hx
  simp [List.mem_range'] at hx
  simp; omega

/-- `∑_{u<N} ∑_{u<w<N} F u w`. -/
private def T (N : Nat) (F : Nat → Nat → Nat) : Nat :=
  ((List.range N).map fun u => ((List.range N).map fun w => if u < w then F u w else 0).sum).sum

private theorem T_succ (N : Nat) (F : Nat → Nat → Nat) :
    T (N + 1) F = T N F + ((List.range N).map fun u => F u N).sum := by
  unfold T
  rw [List.range_succ, List.map_append, List.sum_append]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [sum_map_zero (List.range N) (fun w => if N < w then F N w else 0) (by
    intro x hx; simp at hx; simp; omega)]
  simp only [Nat.lt_irrefl, ite_false, Nat.add_zero]
  rw [← sum_map_add]
  apply sum_map_congr
  intro x hx
  simp at hx
  simp [hx]

private theorem T_closed (k : Nat → Nat) (ind : Nat → Nat → Nat) (N : Nat) :
    T N (fun u w => 3 * k u + 3 * k w + 18 + 9 * ind u w) + 3 * ((List.range N).map k).sum + 9 * N
      = 3 * N * ((List.range N).map k).sum + 9 * N * N + 9 * T N ind := by
  induction N with
  | zero => simp [T]
  | succ N ih =>
    rw [T_succ, T_succ, sum_map_add, sum_map_add, sum_map_add, sum_map_mul, sum_map_mul, sum_map_const,
      sum_map_mul, sum_map_const, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_range]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.add_zero] at ih ⊢
    rw [Nat.mul_comm (k N) N]
    simp only [Nat.mul_assoc] at ih ⊢
    omega


private theorem box_count (n : Nat) (L : List (Nat × Nat)) (h : ∀ e ∈ L, e.1 < n ∧ e.2 < n) :
    ((List.range n).map fun u => ((List.range n).map fun w => L.count (u, w)).sum).sum = L.length := by
  induction L with
  | nil => simp [sum_map_const]
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    have hab := h (a, b) (by simp)
    simp only [List.count_cons, sum_map_add]
    rw [ih (fun e he => h e (by simp [he])), List.length_cons]
    congr 1
    rw [sum_map_congr (g := fun u => if u = a then 1 else 0)]
    · rw [sum_ite_eq, List.count_range]; simp [hab.1]
    intro u _
    by_cases hu : u = a
    · subst hu
      rw [sum_map_congr (g := fun w => if w = b then 1 else 0)]
      · rw [sum_ite_eq, List.count_range]; simp [hab.2]
      intro w _
      by_cases hw : w = b
      · subst hw; simp
      · have : b ≠ w := fun h => hw h.symm
        simp [hw, this]
    · rw [sum_map_zero]
      · simp [hu]
      intro w _
      simp; omega

private theorem sum_up (G : Graph) (hG : G.Valid) :
    ((List.range G.n).map fun u => (G.up u).length).sum = G.edges.length := by
  rw [← box_count G.n G.edges (fun e he => ⟨Nat.lt_trans (hG.2 e he).1 (hG.2 e he).2, (hG.2 e he).2⟩)]
  apply sum_map_congr
  intro u _
  unfold Graph.up
  rw [length_filter_eq]
  apply sum_map_congr
  intro w _
  rw [List.Nodup.count hG.1]
  unfold Graph.isEdge
  by_cases he : (u, w) ∈ G.edges
  · have := (hG.2 _ he).1
    simp [he, this]
  · simp [he]

private theorem T_ind (G : Graph) (hG : G.Valid) :
    T G.n (fun u w => if G.isEdge u w then 1 else 0) = G.edges.length := by
  rw [← sum_up G hG]
  unfold T
  apply sum_map_congr
  intro u _
  unfold Graph.up
  rw [length_filter_eq]
  apply sum_map_congr
  intro w _
  by_cases h1 : u < w <;> by_cases h2 : G.isEdge u w <;> simp [h1, h2]

end SweepCountAux

open SweepCountAux in
theorem sweep_ham_sum (G : Graph) (hG : G.Valid) :
    ((sweepEvents G).map evHam).sum = 3 * G.n * (G.m - 3) + 6 * G.edges.length := by
  have hround : ∀ u ∈ List.range G.n, ((roundEvents G u).map evHam).sum
      = ((List.range G.n).map fun w => if u < w then
          3 * (G.up u).length + 3 * (G.up w).length + 18 + 9 * (if G.isEdge u w then 1 else 0)
          else 0).sum := by
    intro u hu
    have hu : u < G.n := by simpa using hu
    unfold roundEvents
    rw [sum_map_flatMap, ← range'_sum G.n u hu]
    apply sum_map_congr
    intro w hw
    simp [List.mem_range'] at hw
    exact pass_sum G u w (by omega) (by omega)
  have hT := T_closed (fun u => (G.up u).length) (fun u w => if G.isEdge u w then 1 else 0) G.n
  rw [sum_up G hG, T_ind G hG] at hT
  unfold sweepEvents
  rw [List.map_append, List.sum_append, sum_map_flatMap, sum_map_flatMap, sum_map_congr hround,
    sum_map_zero _ _ (fun u _ => completion_sum G u), Nat.add_zero]
  change T G.n _ = _
  unfold Graph.m
  generalize T G.n _ = t at hT ⊢
  generalize G.edges.length = E at hT ⊢
  generalize G.n = N at hT ⊢
  cases N with
  | zero => simp at hT ⊢; omega
  | succ n =>
    have : 3 * (n + 1) + E - 3 = 3 * n + E := by omega
    rw [this]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hT ⊢
    have e1 : n * (3 * n) = 3 * (n * n) := Nat.mul_left_comm n 3 n
    omega


end BraidDistance
