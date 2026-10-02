import BraidDistance.ConstructionBasic
import BraidDistance.Wires

/-!
# The shadow sweep (Lemma 4.1)

* Lemma 4.1: every event can be applied, i.e. the groups it exchanges lie consecutively in the current
  arrangement in the stated order (`sweep_ok`); after all events the arrangement is the reverse of the label
  order (`sweep_final`).
* The arrangements are permutations of the groups (`arrAt_perm`).

Lemma 4.2 is in `SweepPairs.lean`.
-/

namespace BraidDistance

/-- An event can be applied to an arrangement: its groups lie consecutively in the stated order. -/
def EvOK (arr : List Grp) : Ev → Prop
  | .mv g h => ∃ A B, arr = A ++ g :: h :: B
  | .cell u w => ∃ A B, arr = A ++ Grp.X u :: Grp.p u w :: Grp.X w :: B

/-- The pairs of groups exchanged by an event, each in label order. -/
def evPairs : Ev → List (Grp × Grp)
  | .mv g h => [(g, h)]
  | .cell u w => [(.X u, .p u w), (.X u, .X w), (.p u w, .X w)]

/-- All pairs `(x, y)` with `x` before `y` in the list. -/
def orderedPairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ orderedPairs xs

/-! ### Running a list of events -/

/-- Every event of the list can be applied to the running arrangement. -/
private def SW.RunOK : List Grp → List Ev → Prop
  | _, [] => True
  | arr, e :: es => EvOK arr e ∧ SW.RunOK (applyEv arr e) es

/-- The events run from `arr` to `arr'`, each of them applicable. -/
private def SW.Runs (arr : List Grp) (evs : List Ev) (arr' : List Grp) : Prop :=
  SW.RunOK arr evs ∧ evs.foldl applyEv arr = arr'

private theorem SW.runOK_append (arr : List Grp) (e1 e2 : List Ev) :
    SW.RunOK arr (e1 ++ e2) ↔ SW.RunOK arr e1 ∧ SW.RunOK (e1.foldl applyEv arr) e2 := by
  induction e1 generalizing arr with
  | nil => simp [SW.RunOK]
  | cons e es ih => simp [SW.RunOK, ih, and_assoc]

private theorem SW.runs_nil (arr : List Grp) : SW.Runs arr [] arr := ⟨trivial, rfl⟩

private theorem SW.runs_append {a b c : List Grp} {e1 e2 : List Ev} (h1 : SW.Runs a e1 b)
    (h2 : SW.Runs b e2 c) : SW.Runs a (e1 ++ e2) c := by
  refine ⟨(SW.runOK_append a e1 e2).2 ⟨h1.1, ?_⟩, ?_⟩
  · rw [h1.2]; exact h2.1
  · rw [List.foldl_append, h1.2, h2.2]

private theorem SW.runs_congr {a a' b b' : List Grp} {e e' : List Ev} (ha : a = a') (he : e = e')
    (hb : b = b') (h : SW.Runs a' e' b') : SW.Runs a e b := by
  subst ha he hb; exact h

private theorem SW.swapNames_other {g h x : Grp} (hg : x ≠ g) (hh : x ≠ h) : swapNames g h x = x := by
  simp [swapNames, hg, hh]

private theorem SW.map_swapNames {g h : Grp} {A : List Grp} (hg : g ∉ A) (hh : h ∉ A) :
    A.map (swapNames g h) = A := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    simp only [List.mem_cons, not_or] at hg hh
    simp only [List.map_cons, ih hg.2 hh.2]
    rw [SW.swapNames_other (Ne.symm hg.1) (Ne.symm hh.1)]

private theorem SW.nodup_facts {A B : List Grp} {g h : Grp} (hnd : (A ++ g :: h :: B).Nodup) :
    g ∉ A ∧ h ∉ A ∧ g ∉ B ∧ h ∉ B ∧ h ≠ g := by
  obtain ⟨_, hgh, hdis⟩ := List.nodup_append.1 hnd
  have h1 := List.nodup_cons.1 hgh
  have h2 := List.nodup_cons.1 h1.2
  refine ⟨fun hm => hdis g hm g (by simp) rfl, fun hm => hdis h hm h (by simp) rfl,
    fun hm => h1.1 (by simp [hm]), h2.1, fun e => h1.1 (by simp [e])⟩

private theorem SW.step_mv {A B : List Grp} {g h : Grp} (hnd : (A ++ g :: h :: B).Nodup) :
    SW.Runs (A ++ g :: h :: B) [.mv g h] (A ++ h :: g :: B) := by
  refine ⟨⟨⟨A, B, rfl⟩, trivial⟩, ?_⟩
  obtain ⟨hgA, hhA, hgB, hhB, hne⟩ := SW.nodup_facts hnd
  simp [applyEv, SW.map_swapNames hgA hhA, SW.map_swapNames hgB hhB, swapNames, hne]

private theorem SW.step_cell {A B : List Grp} {u w : Nat}
    (hnd : (A ++ Grp.X u :: Grp.p u w :: Grp.X w :: B).Nodup) :
    SW.Runs (A ++ Grp.X u :: Grp.p u w :: Grp.X w :: B) [.cell u w]
      (A ++ Grp.X w :: Grp.p u w :: Grp.X u :: B) := by
  refine ⟨⟨⟨A, B, rfl⟩, trivial⟩, ?_⟩
  have hnd' : (A ++ Grp.X u :: Grp.X w :: (Grp.p u w :: B)).Nodup := by
    refine (List.Perm.nodup_iff ?_).1 hnd
    exact List.Perm.append_left A (List.Perm.cons _ (List.Perm.swap _ _ _))
  obtain ⟨hgA, hhA, hgB, hhB, hne⟩ := SW.nodup_facts hnd'
  simp only [List.mem_cons, not_or] at hgB hhB
  simp [applyEv, SW.map_swapNames hgA hhA, SW.map_swapNames hgB.2 hhB.2, swapNames, hne]

private theorem SW.step_perm {arr : List Grp} {e : Ev} (hnd : arr.Nodup) (hok : EvOK arr e) :
    (applyEv arr e).Perm arr := by
  cases e with
  | mv g h =>
    obtain ⟨A, B, rfl⟩ := hok
    have := (SW.step_mv hnd).2
    simp only [List.foldl] at this
    rw [this]
    exact List.Perm.append_left A (List.Perm.swap g h B)
  | cell u w =>
    obtain ⟨A, B, rfl⟩ := hok
    have := (SW.step_cell hnd).2
    simp only [List.foldl] at this
    rw [this]
    refine List.Perm.append_left A ?_
    exact ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)).trans (List.Perm.swap _ _ _)

private theorem SW.runOK_perm {arr : List Grp} {evs : List Ev} (hnd : arr.Nodup) (hok : SW.RunOK arr evs) :
    (evs.foldl applyEv arr).Perm arr := by
  induction evs generalizing arr with
  | nil => exact List.Perm.refl _
  | cons e es ih =>
    have hp := SW.step_perm hnd hok.1
    exact (ih (hp.nodup_iff.2 hnd) hok.2).trans hp

private theorem SW.runs_nodup {a b : List Grp} {e : List Ev} (h : SW.Runs a e b) (hnd : a.Nodup) :
    b.Nodup := by
  rw [← h.2]; exact (SW.runOK_perm hnd h.1).nodup_iff.2 hnd

/-- `h` passes up through `Ps`. -/
private theorem SW.passUp (Ps : List Grp) (A B : List Grp) (h : Grp) (hnd : (A ++ Ps ++ h :: B).Nodup) :
    SW.Runs (A ++ Ps ++ h :: B) (Ps.reverse.map fun g => Ev.mv g h) (A ++ h :: Ps ++ B) := by
  induction Ps generalizing A with
  | nil => exact SW.runs_congr (by simp) rfl (by simp) (SW.runs_nil (A ++ h :: B))
  | cons x Ps ih =>
    have h1 := ih (A ++ [x]) (by simpa using hnd)
    have hnd2 := SW.runs_nodup h1 (by simpa using hnd)
    have h2 := SW.step_mv (A := A) (g := x) (h := h) (B := Ps ++ B) (by simpa using hnd2)
    have := SW.runs_append h1 (SW.runs_congr (by simp) rfl rfl h2)
    exact SW.runs_congr (by simp) (by simp) (by simp) this

/-- The groups `hs` pass up through `Bu` one after another. -/
private theorem SW.passMany (Bu : List Grp) (hs A D : List Grp) (hnd : (A ++ Bu ++ hs ++ D).Nodup) :
    SW.Runs (A ++ Bu ++ hs ++ D) (hs.flatMap fun h => Bu.reverse.map fun g => Ev.mv g h)
      (A ++ hs ++ Bu ++ D) := by
  induction hs generalizing A with
  | nil => exact SW.runs_congr rfl rfl (by simp) (SW.runs_nil _)
  | cons h hs ih =>
    have h1 := SW.passUp Bu A (hs ++ D) h (by simpa using hnd)
    have hnd2 := SW.runs_nodup h1 (by simpa using hnd)
    have h2 := ih (A ++ [h]) (by simpa using hnd2)
    have := SW.runs_append h1 (SW.runs_congr (by simp) rfl rfl h2)
    exact SW.runs_congr (by simp) (by simp) (by simp) this

/-! ### One bundle passing up through another, abstractly -/

/-- `B_w` passes up through `B_u = (below, X_u, ab)` when `uw` is not an edge. -/
private theorem SW.pass_nonedge (C below ab Pw D : List Grp) (Xu Xw : Grp)
    (hnd : (C ++ below ++ [Xu] ++ ab ++ [Xw] ++ Pw ++ D).Nodup) :
    SW.Runs (C ++ below ++ [Xu] ++ ab ++ [Xw] ++ Pw ++ D)
      ((ab.reverse.map fun g => Ev.mv g Xw) ++ [Ev.mv Xu Xw] ++ (below.reverse.map fun g => Ev.mv g Xw) ++
        Pw.flatMap fun h => (below ++ [Xu] ++ ab).reverse.map fun g => Ev.mv g h)
      (C ++ Xw :: Pw ++ (below ++ [Xu] ++ ab) ++ D) := by
  have h1 := SW.passUp ab (C ++ below ++ [Xu]) (Pw ++ D) Xw (by simpa using hnd)
  have hn1 := SW.runs_nodup h1 (by simpa using hnd)
  have h2 := SW.step_mv (A := C ++ below) (g := Xu) (h := Xw) (B := ab ++ Pw ++ D) (by simpa using hn1)
  have hn2 := SW.runs_nodup h2 (by simpa using hn1)
  have h3 := SW.passUp below C (Xu :: ab ++ Pw ++ D) Xw (by simpa using hn2)
  have hn3 := SW.runs_nodup h3 (by simpa using hn2)
  have h4 := SW.passMany (below ++ [Xu] ++ ab) Pw (C ++ [Xw]) D (by simpa using hn3)
  have := SW.runs_append (SW.runs_append (SW.runs_append h1 (SW.runs_congr (by simp) rfl rfl h2))
    (SW.runs_congr (by simp) rfl rfl h3)) (SW.runs_congr (by simp) rfl rfl h4)
  exact SW.runs_congr (by simp) (by simp) (by simp) this

/-- `B_w` passes up through `B_u = (below, X_u, p_uw, ab)` when `uw` is an edge. -/
private theorem SW.pass_edge (C below ab Pw D : List Grp) (u w : Nat)
    (hnd : (C ++ below ++ [Grp.X u, Grp.p u w] ++ ab ++ [Grp.X w] ++ Pw ++ D).Nodup) :
    SW.Runs (C ++ below ++ [Grp.X u, Grp.p u w] ++ ab ++ [Grp.X w] ++ Pw ++ D)
      ((ab.reverse.map fun g => Ev.mv g (Grp.X w)) ++ [Ev.cell u w] ++
        (below.reverse.map fun g => Ev.mv g (Grp.X w)) ++
        Pw.flatMap fun h => (below ++ [Grp.p u w, Grp.X u] ++ ab).reverse.map fun g => Ev.mv g h)
      (C ++ Grp.X w :: Pw ++ (below ++ [Grp.p u w, Grp.X u] ++ ab) ++ D) := by
  have h1 := SW.passUp ab (C ++ below ++ [Grp.X u, Grp.p u w]) (Pw ++ D) (Grp.X w) (by simpa using hnd)
  have hn1 := SW.runs_nodup h1 (by simpa using hnd)
  have h2 := SW.step_cell (A := C ++ below) (u := u) (w := w) (B := ab ++ Pw ++ D) (by simpa using hn1)
  have hn2 := SW.runs_nodup h2 (by simpa using hn1)
  have h3 := SW.passUp below C (Grp.p u w :: Grp.X u :: ab ++ Pw ++ D) (Grp.X w) (by simpa using hn2)
  have hn3 := SW.runs_nodup h3 (by simpa using hn2)
  have h4 := SW.passMany (below ++ [Grp.p u w, Grp.X u] ++ ab) Pw (C ++ [Grp.X w]) D (by simpa using hn3)
  have := SW.runs_append (SW.runs_append (SW.runs_append h1 (SW.runs_congr (by simp) rfl rfl h2))
    (SW.runs_congr (by simp) rfl rfl h3)) (SW.runs_congr (by simp) rfl rfl h4)
  exact SW.runs_congr (by simp) (by simp) (by simp) this

/-- The private wires `ps` are reversed by the completion events. -/
private theorem SW.complete_partial (ps A B : List Grp) (hnd : (A ++ ps ++ B).Nodup) :
    ∀ j, j ≤ ps.length → SW.Runs (A ++ ps ++ B)
      ((List.range j).flatMap fun i => (ps.take i).map fun g => Ev.mv g (ps.getD i (.X 0)))
      (A ++ (ps.take j).reverse ++ ps.drop j ++ B)
  | 0, _ => SW.runs_congr rfl rfl (by simp) (SW.runs_nil _)
  | j + 1, hj => by
    have ih := SW.complete_partial ps A B hnd j (by omega)
    have hlt : j < ps.length := by omega
    have e := List.drop_eq_getElem_cons hlt
    have hp := SW.passUp (ps.take j).reverse A (ps.drop (j + 1) ++ B) ps[j] (by
      have := SW.runs_nodup ih hnd
      rw [e] at this; simp only [List.append_assoc, List.cons_append] at this ⊢; exact this)
    have := SW.runs_append ih (SW.runs_congr (by rw [e]; simp only [List.append_assoc, List.cons_append])
      rfl rfl hp)
    refine SW.runs_congr rfl ?_ ?_ this
    · rw [List.range_succ, List.flatMap_append]; simp [List.getD, hlt]
    · rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      simp only [Option.toList, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc]

/-! ### The neighbours above a vertex -/

private theorem SW.mem_up {G : Graph} {u x : Nat} :
    x ∈ G.up u ↔ x < G.n ∧ u < x ∧ G.isEdge u x = true := by
  simp [Graph.up]

private theorem SW.up_pairwise (G : Graph) (u : Nat) : (G.up u).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

private theorem SW.filter_split {L : List Nat} (hL : L.Pairwise (· < ·)) {w : Nat} (hw : w ∈ L) :
    L.filter (· < w + 1) = L.filter (· < w) ++ [w] ∧ L.filter (w ≤ ·) = w :: L.filter (w < ·) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hw
  have hp := List.pairwise_append.1 hL
  have hs : ∀ x ∈ s, x < w := fun x hx => hp.2.2 x hx w (by simp)
  have ht : ∀ x ∈ t, w < x := (List.pairwise_cons.1 hp.2.1).1
  have e1 : s.filter (· < w + 1) = s :=
    List.filter_eq_self.2 (fun x hx => by have := hs x hx; simp; omega)
  have e2 : s.filter (· < w) = s := List.filter_eq_self.2 (fun x hx => by simpa using hs x hx)
  have e3 : t.filter (· < w + 1) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by have := ht x hx; simp; omega)
  have e4 : t.filter (· < w) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by have := ht x hx; simp; omega)
  have e5 : s.filter (w ≤ ·) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by have := hs x hx; simp; omega)
  have e6 : s.filter (w < ·) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by have := hs x hx; simp; omega)
  have e7 : t.filter (w ≤ ·) = t :=
    List.filter_eq_self.2 (fun x hx => by have := ht x hx; simp; omega)
  have e8 : t.filter (w < ·) = t := List.filter_eq_self.2 (fun x hx => by simpa using ht x hx)
  simp [List.filter_append, e1, e2, e3, e4, e5, e6, e7, e8]

/-! ### The arrangements of Lemma 4.1(b) -/

private def SW.Plt (G : Graph) (u w : Nat) : List Grp := ((G.up u).filter (· < w)).map (Grp.p u)
private def SW.Pge (G : Graph) (u w : Nat) : List Grp := ((G.up u).filter (w ≤ ·)).map (Grp.p u)
private def SW.Pgt (G : Graph) (u w : Nat) : List Grp := ((G.up u).filter (w < ·)).map (Grp.p u)

private theorem SW.passEvents_eq (G : Graph) (u w : Nat) : passEvents G u w =
    if G.isEdge u w then
      ((SW.Pgt G u w).reverse.map fun g => Ev.mv g (.X w)) ++ [Ev.cell u w] ++
        ((SW.Plt G u w).reverse.map fun g => Ev.mv g (.X w)) ++
        ((G.up w).map (Grp.p w)).flatMap fun h =>
          (SW.Plt G u w ++ [Grp.p u w, Grp.X u] ++ SW.Pgt G u w).reverse.map fun g => Ev.mv g h
    else
      ((SW.Pge G u w).reverse.map fun g => Ev.mv g (.X w)) ++ [Ev.mv (.X u) (.X w)] ++
        ((SW.Plt G u w).reverse.map fun g => Ev.mv g (.X w)) ++
        ((G.up w).map (Grp.p w)).flatMap fun h =>
          (SW.Plt G u w ++ [Grp.X u] ++ SW.Pge G u w).reverse.map fun g => Ev.mv g h := rfl

/-- The bundles `B_s, …, B_{s+len-1}`. -/
private def SW.Bs (G : Graph) (s len : Nat) : List Grp := (List.range' s len).flatMap (bundle G)
/-- `B'_v = (Π_v, X_v)`. -/
private def SW.Bp (G : Graph) (v : Nat) : List Grp := (G.up v).map (Grp.p v) ++ [Grp.X v]
/-- `B'_{u-1}, …, B'_0`. -/
private def SW.Rest (G : Graph) (u : Nat) : List Grp := (List.range u).reverse.flatMap (SW.Bp G)
/-- `(Π_u^{<w}, X_u, Π_u^{≥w})`. -/
private def SW.Mid (G : Graph) (u w : Nat) : List Grp := SW.Plt G u w ++ [Grp.X u] ++ SW.Pge G u w
/-- The arrangement before `B_{u+1+d}` passes through `B_u`. -/
private def SW.R (G : Graph) (u d : Nat) : List Grp :=
  SW.Bs G (u + 1) d ++ SW.Mid G u (u + 1 + d) ++ SW.Bs G (u + 1 + d) (G.n - (u + 1 + d)) ++ SW.Rest G u
/-- The arrangement at the start of round `u`. -/
private def SW.Start (G : Graph) (u : Nat) : List Grp := SW.Bs G u (G.n - u) ++ SW.Rest G u

private theorem SW.Bs_cons (G : Graph) (s d : Nat) : SW.Bs G s (d + 1) = bundle G s ++ SW.Bs G (s + 1) d := by
  simp [SW.Bs, List.range'_succ]

private theorem SW.Bs_succ_right (G : Graph) (s d : Nat) :
    SW.Bs G s (d + 1) = SW.Bs G s d ++ bundle G (s + d) := by
  simp [SW.Bs, List.range'_concat, List.flatMap_append]

private theorem SW.Bs_zero (G : Graph) (s : Nat) : SW.Bs G s 0 = [] := rfl

/-- `B_w` passes up through `B_u` (Lemma 4.1(b)). -/
private theorem SW.pass (G : Graph) {u d : Nat} (hw : u + 1 + d < G.n) (hnd : (SW.R G u d).Nodup) :
    SW.Runs (SW.R G u d) (passEvents G u (u + 1 + d)) (SW.R G u (d + 1)) := by
  have eR0 : SW.R G u d = SW.Bs G (u + 1) d ++ SW.Mid G u (u + 1 + d) ++
      (Grp.X (u + 1 + d) :: (G.up (u + 1 + d)).map (Grp.p (u + 1 + d))) ++
      (SW.Bs G (u + 1 + d + 1) (G.n - (u + 1 + d + 1)) ++ SW.Rest G u) := by
    have : G.n - (u + 1 + d) = (G.n - (u + 1 + d + 1)) + 1 := by omega
    simp only [SW.R, this, SW.Bs_cons, bundle, List.append_assoc]
  have eR1 : SW.R G u (d + 1) = SW.Bs G (u + 1) d ++
      Grp.X (u + 1 + d) :: (G.up (u + 1 + d)).map (Grp.p (u + 1 + d)) ++ SW.Mid G u (u + 1 + d + 1) ++
      (SW.Bs G (u + 1 + d + 1) (G.n - (u + 1 + d + 1)) ++ SW.Rest G u) := by
    have h1 : u + 1 + (d + 1) = u + 1 + d + 1 := by omega
    simp only [SW.R, h1, SW.Bs_succ_right, bundle, List.append_assoc, List.cons_append]
  rw [eR0] at hnd
  rw [eR0, eR1, SW.passEvents_eq]
  have huw : u < u + 1 + d := by omega
  generalize u + 1 + d = w at hw hnd huw ⊢
  cases hE : G.isEdge u w with
  | false =>
    have hnm : w ∉ G.up u := fun h => by rw [SW.mem_up, hE] at h; simp at h
    have hM : SW.Mid G u (w + 1) = SW.Mid G u w := by
      have c1 : (G.up u).filter (· < w + 1) = (G.up u).filter (· < w) :=
        List.filter_congr (fun x hx => by
          have : x ≠ w := fun e => hnm (e ▸ hx)
          simp only [decide_eq_decide]; omega)
      have c2 : (G.up u).filter (w + 1 ≤ ·) = (G.up u).filter (w ≤ ·) :=
        List.filter_congr (fun x hx => by
          have : x ≠ w := fun e => hnm (e ▸ hx)
          simp only [decide_eq_decide]; omega)
      simp only [SW.Mid, SW.Plt, SW.Pge, c1, c2]
    rw [hM]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SW.runs_congr (by simp [SW.Mid]) rfl (by simp [SW.Mid])
      (SW.pass_nonedge (SW.Bs G (u + 1) d) (SW.Plt G u w) (SW.Pge G u w) ((G.up w).map (Grp.p w))
        (SW.Bs G (w + 1) (G.n - (w + 1)) ++ SW.Rest G u) (.X u) (.X w) (by simpa [SW.Mid] using hnd))
  | true =>
    have hm : w ∈ G.up u := SW.mem_up.2 ⟨hw, huw, hE⟩
    obtain ⟨f1, f2⟩ := SW.filter_split (SW.up_pairwise G u) hm
    have c3 : (G.up u).filter (w + 1 ≤ ·) = (G.up u).filter (w < ·) :=
      List.filter_congr (fun x _ => by simp only [decide_eq_decide]; omega)
    have hM0 : SW.Mid G u w = SW.Plt G u w ++ [Grp.X u, Grp.p u w] ++ SW.Pgt G u w := by
      simp [SW.Mid, SW.Pge, SW.Pgt, f2]
    have hM1 : SW.Mid G u (w + 1) = SW.Plt G u w ++ [Grp.p u w, Grp.X u] ++ SW.Pgt G u w := by
      simp [SW.Mid, SW.Plt, SW.Pge, SW.Pgt, f1, c3]
    rw [hM0] at hnd
    rw [hM0, hM1]
    simp only [↓reduceIte]
    exact SW.runs_congr (by simp) rfl (by simp)
      (SW.pass_edge (SW.Bs G (u + 1) d) (SW.Plt G u w) (SW.Pgt G u w) ((G.up w).map (Grp.p w))
        (SW.Bs G (w + 1) (G.n - (w + 1)) ++ SW.Rest G u) u w (by simpa using hnd))

/-! ### The rounds -/

private theorem SW.round_partial (G : Graph) {u : Nat} (hnd : (SW.R G u 0).Nodup) :
    ∀ d, u + 1 + d ≤ G.n →
      SW.Runs (SW.R G u 0) ((List.range' (u + 1) d).flatMap (passEvents G u)) (SW.R G u d)
  | 0, _ => SW.runs_nil _
  | d + 1, hd => by
    have ih := SW.round_partial G hnd d (by omega)
    have hp := SW.pass G (u := u) (d := d) (by omega) (SW.runs_nodup ih hnd)
    exact SW.runs_congr rfl (by rw [List.range'_concat, List.flatMap_append]; simp) rfl
      (SW.runs_append ih hp)

private theorem SW.Plt_succ (G : Graph) (u : Nat) : SW.Plt G u (u + 1) = [] := by
  simp only [SW.Plt]
  rw [List.filter_eq_nil_iff.2 (fun x hx => by have := (SW.mem_up.1 hx).2.1; simp; omega)]
  rfl

private theorem SW.Pge_succ (G : Graph) (u : Nat) : SW.Pge G u (u + 1) = (G.up u).map (Grp.p u) := by
  simp only [SW.Pge]
  rw [List.filter_eq_self.2 (fun x hx => by have := (SW.mem_up.1 hx).2.1; simp; omega)]

private theorem SW.Plt_n (G : Graph) (u : Nat) : SW.Plt G u G.n = (G.up u).map (Grp.p u) := by
  simp only [SW.Plt]
  rw [List.filter_eq_self.2 (fun x hx => by have := (SW.mem_up.1 hx).1; simp; omega)]

private theorem SW.Pge_n (G : Graph) (u : Nat) : SW.Pge G u G.n = [] := by
  simp only [SW.Pge]
  rw [List.filter_eq_nil_iff.2 (fun x hx => by have := (SW.mem_up.1 hx).1; simp; omega)]
  rfl

private theorem SW.R_zero (G : Graph) {u : Nat} (hu : u < G.n) : SW.R G u 0 = SW.Start G u := by
  have : G.n - u = (G.n - (u + 1)) + 1 := by omega
  simp only [SW.R, SW.Start, SW.Mid, Nat.add_zero, SW.Plt_succ, SW.Pge_succ, SW.Bs_zero, this, SW.Bs_cons,
    bundle]
  simp

private theorem SW.R_last (G : Graph) {u : Nat} (hu : u < G.n) :
    SW.R G u (G.n - (u + 1)) = SW.Start G (u + 1) := by
  have h1 : u + 1 + (G.n - (u + 1)) = G.n := by omega
  simp only [SW.R, SW.Start, SW.Mid, h1, SW.Plt_n, SW.Pge_n, Nat.sub_self, SW.Bs_zero, SW.Rest,
    List.range_succ, List.reverse_append, List.flatMap_append]
  simp [SW.Bp]

private theorem SW.round (G : Graph) {u : Nat} (hu : u < G.n) (hnd : (SW.Start G u).Nodup) :
    SW.Runs (SW.Start G u) (roundEvents G u) (SW.Start G (u + 1)) := by
  rw [← SW.R_zero G hu] at hnd ⊢
  rw [← SW.R_last G hu]
  exact SW.round_partial G hnd _ (by omega)

private def SW.vtx : Grp → Nat
  | .X u => u
  | .p u _ => u

private theorem SW.vtx_bundle {G : Graph} {u : Nat} {x : Grp} (hx : x ∈ bundle G u) : SW.vtx x = u := by
  simp only [bundle, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨w, _, rfl⟩ <;> rfl

private theorem SW.labelOrder_nodup (G : Graph) : (labelOrder G).Nodup := by
  unfold labelOrder
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · rw [← List.nodup_iff_pairwise_ne]
    simp only [bundle]
    rw [List.nodup_cons]
    refine ⟨by simp, ?_⟩
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact (SW.up_pairwise G u).imp (fun h e => by cases e; exact Nat.lt_irrefl _ h)
  · refine List.pairwise_lt_range.imp ?_
    intro a b hab x hx y hy hxy
    have h1 := SW.vtx_bundle hx
    have h2 := SW.vtx_bundle hy
    subst hxy; omega

private theorem SW.Start_zero (G : Graph) : SW.Start G 0 = labelOrder G := by
  simp [SW.Start, SW.Bs, SW.Rest, labelOrder, List.range_eq_range']

private theorem SW.rounds (G : Graph) : ∀ u, u ≤ G.n →
    SW.Runs (labelOrder G) ((List.range u).flatMap (roundEvents G)) (SW.Start G u)
  | 0, _ => SW.runs_congr rfl rfl (SW.Start_zero G) (SW.runs_nil _)
  | u + 1, hu => by
    have ih := SW.rounds G u (by omega)
    have hr := SW.round G (by omega) (SW.runs_nodup ih (SW.labelOrder_nodup G))
    exact SW.runs_congr rfl (by rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]) rfl
      (SW.runs_append ih hr)

/-! ### The completion -/

private theorem SW.flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- The arrangement after the completion of the vertices `v < k`. -/
private def SW.Fin (G : Graph) (k : Nat) : List Grp :=
  (List.range G.n).reverse.flatMap fun v => if v < k then (bundle G v).reverse else SW.Bp G v

private theorem SW.range_split {n k : Nat} (hk : k < n) :
    List.range n = List.range k ++ k :: List.range' (k + 1) (n - k - 1) := by
  rw [List.range_eq_range', List.range_eq_range']
  have e : n = k + ((n - k - 1) + 1) := by omega
  conv => lhs; rw [e]
  rw [← List.range'_append]
  simp [List.range'_succ]

private theorem SW.complete_step (G : Graph) {k : Nat} (hk : k < G.n) (hnd : (SW.Fin G k).Nodup) :
    SW.Runs (SW.Fin G k) (completionEvents G k) (SW.Fin G (k + 1)) := by
  have hs := SW.range_split hk
  have eF0 : SW.Fin G k = (List.range' (k + 1) (G.n - k - 1)).reverse.flatMap (SW.Bp G) ++
      (G.up k).map (Grp.p k) ++ ([Grp.X k] ++ (List.range k).reverse.flatMap fun v => (bundle G v).reverse) := by
    unfold SW.Fin
    rw [hs, List.reverse_append, List.reverse_cons, List.flatMap_append, List.flatMap_append,
      List.flatMap_singleton]
    rw [SW.flatMap_congr (l := (List.range' (k + 1) _).reverse) (g := SW.Bp G)
      (fun v hv => by simp at hv; simp; omega)]
    rw [SW.flatMap_congr (l := (List.range k).reverse) (g := fun v => (bundle G v).reverse)
      (fun v hv => by simp at hv; simp [hv])]
    simp [SW.Bp]
  have eF1 : SW.Fin G (k + 1) = (List.range' (k + 1) (G.n - k - 1)).reverse.flatMap (SW.Bp G) ++
      ((G.up k).map (Grp.p k)).reverse ++
      ([Grp.X k] ++ (List.range k).reverse.flatMap fun v => (bundle G v).reverse) := by
    unfold SW.Fin
    rw [hs, List.reverse_append, List.reverse_cons, List.flatMap_append, List.flatMap_append,
      List.flatMap_singleton]
    rw [SW.flatMap_congr (l := (List.range' (k + 1) _).reverse) (g := SW.Bp G)
      (fun v hv => by simp at hv; simp; omega)]
    rw [SW.flatMap_congr (l := (List.range k).reverse) (g := fun v => (bundle G v).reverse)
      (fun v hv => by simp at hv; simp; omega)]
    simp [bundle]
  rw [eF0] at hnd
  rw [eF0, eF1]
  have := SW.complete_partial ((G.up k).map (Grp.p k)) _ _ hnd _ (Nat.le_refl _)
  exact SW.runs_congr rfl rfl (by rw [List.take_length, List.drop_length]; simp) this

private theorem SW.completes (G : Graph) (hnd : (SW.Fin G 0).Nodup) : ∀ k, k ≤ G.n →
    SW.Runs (SW.Fin G 0) ((List.range k).flatMap (completionEvents G)) (SW.Fin G k)
  | 0, _ => SW.runs_nil _
  | k + 1, hk => by
    have ih := SW.completes G hnd k (by omega)
    have hc := SW.complete_step G (k := k) (by omega) (SW.runs_nodup ih hnd)
    exact SW.runs_congr rfl (by rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]) rfl
      (SW.runs_append ih hc)

private theorem SW.Start_n (G : Graph) : SW.Start G G.n = SW.Fin G 0 := by
  simp [SW.Start, SW.Bs_zero, SW.Fin, SW.Rest]

private theorem SW.Fin_n (G : Graph) : SW.Fin G G.n = (labelOrder G).reverse := by
  unfold SW.Fin labelOrder
  rw [List.reverse_flatMap]
  exact SW.flatMap_congr (fun v hv => by simp at hv; simp [hv])

/-- The whole sweep runs from the label order to its reverse. -/
private theorem SW.sweep_runs (G : Graph) :
    SW.Runs (labelOrder G) (sweepEvents G) (labelOrder G).reverse := by
  have h1 := SW.rounds G G.n (Nat.le_refl _)
  rw [SW.Start_n] at h1
  have h2 := SW.completes G (SW.runs_nodup h1 (SW.labelOrder_nodup G)) G.n (Nat.le_refl _)
  rw [SW.Fin_n] at h2
  exact SW.runs_append h1 h2

private theorem SW.runOK_take {arr : List Grp} {evs : List Ev} (h : SW.RunOK arr evs) (k : Nat) :
    SW.RunOK arr (evs.take k) :=
  ((SW.runOK_append arr (evs.take k) (evs.drop k)).1 (by rw [List.take_append_drop]; exact h)).1

private theorem SW.runOK_get {arr : List Grp} {evs : List Ev} (h : SW.RunOK arr evs) {k : Nat}
    (hk : k < evs.length) : EvOK ((evs.take k).foldl applyEv arr) (evs.getD k (.cell 0 0)) := by
  have := ((SW.runOK_append arr (evs.take k) (evs.drop k)).1 (by rw [List.take_append_drop]; exact h)).2
  rw [List.drop_eq_getElem_cons hk] at this
  have e : evs.getD k (.cell 0 0) = evs[k] := by simp [List.getD, hk]
  rw [e]; exact this.1

/-- Lemma 4.1(b), (c): every event can be applied. -/
theorem sweep_ok (G : Graph) (_hG : G.Valid) {k : Nat} (hk : k < numFactors G) :
    EvOK (arrAt G k) (evAt G k) :=
  SW.runOK_get (SW.sweep_runs G).1 hk

/-- Lemma 4.1(d): the sweep reverses the label order. -/
theorem sweep_final (G : Graph) (_hG : G.Valid) : arrAt G (numFactors G) = (labelOrder G).reverse := by
  unfold arrAt numFactors
  rw [List.take_length]
  exact (SW.sweep_runs G).2

/-- The arrangements are permutations of the groups. -/
theorem arrAt_perm (G : Graph) (_hG : G.Valid) {k : Nat} (_hk : k ≤ numFactors G) :
    (arrAt G k).Perm (labelOrder G) :=
  SW.runOK_perm (SW.labelOrder_nodup G) (SW.runOK_take (SW.sweep_runs G).1 k)

end BraidDistance
