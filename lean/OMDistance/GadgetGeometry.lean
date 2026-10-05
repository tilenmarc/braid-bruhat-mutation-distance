import OMDistance.Minors
import OMDistance.Instances
import BraidDistance.Chain

/-!
# Gadgets with the element ∞ (the geometry of Proposition 7.1)

For a valid graph `G` with `m = G.m` wires, the positive fibres live on `[m+1]` with `∞ = m`.

* `gadgetZ G e = A_e ∪ {∞}`: the seven wires `A_e = X_u ∪ {p_e} ∪ X_w` of the edge `e = uw` (Part I's
  `edgeWires`, increasing) followed by `∞ = m`; eight labels in increasing order.  Restricting
  `Pos₃ s_G`, `Pos₃ v_G` to it gives `Pos₃ g^s`, `Pos₃ g^v` (`gadgetZ_restrict`, from Corollary 4.6(a)).
* `InGadget G e B`: the basis `B` lies inside `A_e ∪ {∞}`.
* `bigT G u = 𝒯_u`: the four bases inside `X_u ∪ {∞}`, namely `X_u` and `{x, x', ∞}` for `x < x'` in `X_u`
  (`X_u = {f, f+1, f+2}` with `f = firstWire G (.X u)`).  They replace the bead triples of Proposition 5.1.

The overlap facts of the proof of Proposition 7.1: the sets `𝒯_u` are pairwise disjoint (`bigT_disjoint`); a basis
of `𝒯_x` inside `A_e ∪ {∞}` has `x ∈ e` (`bigT_inGadget`); and a basis inside `A_e ∪ {∞}` and `A_f ∪ {∞}` for
distinct edges `e, f` lies in some `𝒯_u` (`gadget_overlap`), since `A_e ∩ A_f` is `X_u` if `e ∩ f = {u}` and empty
otherwise.  The needed wire facts are in Part I (`edgeWires_spec`, `wiresOf_disjoint`, `mem_labelOrder`,
`wiresOf_lt`, `edge_restrict`).
-/

namespace OMDistance

open BraidDistance (StrictIncr Graph Grp edgeWires firstWire gs gv)

/-- `A_e ∪ {∞}`: the wires of the gadget of `e`, followed by `∞ = m`. -/
def gadgetZ (G : Graph) (e : Nat × Nat) : List Nat := edgeWires G e.1 e.2 ++ [G.m]

/-- The four bases inside `X_u ∪ {∞}`. -/
def bigT (G : Graph) (u : Nat) : List (List Nat) :=
  [[firstWire G (.X u), firstWire G (.X u) + 1, firstWire G (.X u) + 2],
   [firstWire G (.X u), firstWire G (.X u) + 1, G.m],
   [firstWire G (.X u), firstWire G (.X u) + 2, G.m],
   [firstWire G (.X u) + 1, firstWire G (.X u) + 2, G.m]]

/-- `B ⊆ A_e ∪ {∞}`. -/
def InGadget (G : Graph) (e : Nat × Nat) (B : List Nat) : Prop := ∀ x ∈ B, x ∈ gadgetZ G e

private theorem gg_X_mem (G : Graph) (hG : G.Valid) {u : Nat} (hu : u < G.n) :
    BraidDistance.Grp.X u ∈ BraidDistance.labelOrder G :=
  (BraidDistance.mem_labelOrder G hG _).2 (Or.inl ⟨u, hu, rfl⟩)

private theorem gg_edge_mem (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    BraidDistance.Grp.X e.1 ∈ BraidDistance.labelOrder G ∧ BraidDistance.Grp.p e.1 e.2 ∈ BraidDistance.labelOrder G ∧
      BraidDistance.Grp.X e.2 ∈ BraidDistance.labelOrder G := by
  have hv := hG.2 _ he
  refine ⟨gg_X_mem G hG (by omega), (BraidDistance.mem_labelOrder G hG _).2 (Or.inr ⟨e.1, e.2, he, rfl⟩),
    gg_X_mem G hG hv.2⟩

private theorem gg_wiresOf_X (G : Graph) (u : Nat) :
    BraidDistance.wiresOf G (.X u) = [firstWire G (.X u), firstWire G (.X u) + 1, firstWire G (.X u) + 2] := rfl

/-- A wire lies in the wires of at most one group. -/
private theorem gg_owner (G : Graph) {g h : Grp} (hg : g ∈ BraidDistance.labelOrder G)
    (hh : h ∈ BraidDistance.labelOrder G) {x : Nat}
    (hxg : x ∈ BraidDistance.wiresOf G g) (hxh : x ∈ BraidDistance.wiresOf G h) : g = h := by
  by_cases e : g = h
  · exact e
  · exact absurd hxh (BraidDistance.wiresOf_disjoint G hg hh e x hxg)

/-- Every wire common to `A_e` and `A_f` (`e ≠ f`) is a wire of the block of a common endpoint. -/
private theorem gg_common (G : Graph) (hG : G.Valid) {e f : Nat × Nat} (he : e ∈ G.edges)
    (hf : f ∈ G.edges) (hef : e ≠ f) : ∀ x, x ∈ edgeWires G e.1 e.2 → x ∈ edgeWires G f.1 f.2 →
      ∃ c, (c = e.1 ∨ c = e.2) ∧ (c = f.1 ∨ c = f.2) ∧ x ∈ BraidDistance.wiresOf G (.X c) := by
  obtain ⟨e1, e2, e3⟩ := gg_edge_mem G hG he
  obtain ⟨f1, f2, f3⟩ := gg_edge_mem G hG hf
  intro x hxe hxf
  simp only [edgeWires, List.mem_append] at hxe hxf
  rcases hxe with (hxe | hxe) | hxe <;> rcases hxf with (hxf | hxf) | hxf
  · have := gg_owner G e1 f1 hxe hxf; injection this with q
    exact ⟨e.1, Or.inl rfl, Or.inl q, hxe⟩
  · have := gg_owner G e1 f2 hxe hxf; cases this
  · have := gg_owner G e1 f3 hxe hxf; injection this with q
    exact ⟨e.1, Or.inl rfl, Or.inr q, hxe⟩
  · have := gg_owner G e2 f1 hxe hxf; cases this
  · have := gg_owner G e2 f2 hxe hxf
    injection this with q1 q2
    exact absurd (Prod.ext q1 q2) hef
  · have := gg_owner G e2 f3 hxe hxf; cases this
  · have := gg_owner G e3 f1 hxe hxf; injection this with q
    exact ⟨e.2, Or.inr rfl, Or.inl q, hxe⟩
  · have := gg_owner G e3 f2 hxe hxf; cases this
  · have := gg_owner G e3 f3 hxe hxf; injection this with q
    exact ⟨e.2, Or.inr rfl, Or.inr q, hxe⟩

/-- The block of `u` ends before `m`. -/
private theorem gg_fw_bound (G : Graph) (hG : G.Valid) {u : Nat} (hu : u < G.n) :
    firstWire G (.X u) + 2 < G.m :=
  BraidDistance.wiresOf_lt G hG (gg_X_mem G hG hu) _ (by simp [gg_wiresOf_X])

/-- Every member of `𝒯_u` starts with a wire of `X_u`. -/
private theorem gg_bigT_head (G : Graph) {u : Nat} {B : List Nat} (hB : B ∈ bigT G u) :
    ∃ x B', B = x :: B' ∧ x ∈ BraidDistance.wiresOf G (.X u) := by
  simp only [bigT, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, by simp [gg_wiresOf_X]⟩

private theorem gg_getD_lt {E : List Nat} {m i : Nat} (hi : i < E.length) :
    (E ++ [m]).getD i 0 = E.getD i 0 ∧ E.getD i 0 ∈ E := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi,
    Option.getD_some]
  exact ⟨trivial, List.getElem_mem hi⟩

private theorem gg_getD_end {E : List Nat} {m : Nat} : (E ++ [m]).getD E.length 0 = m := by
  simp [List.getD_eq_getElem?_getD]

theorem gadgetZ_spec (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    StrictIncr (gadgetZ G e) ∧ (gadgetZ G e).length = 8 ∧ ∀ x ∈ gadgetZ G e, x < G.m + 1 := by
  obtain ⟨hinc, hlen, hlt⟩ := BraidDistance.edgeWires_spec G hG he
  refine ⟨?_, ?_, ?_⟩
  · unfold gadgetZ StrictIncr
    rw [List.pairwise_append]
    refine ⟨hinc, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hlt a ha
  · simp [gadgetZ, hlen]
  · intro x hx
    simp only [gadgetZ, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · have := hlt x hx; omega
    · omega

/-- Corollary 4.6(a) with `∞`: the restrictions of `Pos₃ s_G` and `Pos₃ v_G` to `A_e ∪ {∞}` are `Pos₃ g^s` and
`Pos₃ g^v`. -/
theorem gadgetZ_restrict (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    AgreeR 8 3 (restrictR (gadgetZ G e) (posF G.m (sMap G))) (posF 7 (ofSMap gs)) ∧
      AgreeR 8 3 (restrictR (gadgetZ G e) (posF G.m (vMap G))) (posF 7 (ofSMap gv)) := by
  obtain ⟨_, hlen, hlt⟩ := BraidDistance.edgeWires_spec G hG he
  obtain ⟨hs, hv⟩ := BraidDistance.edge_restrict G hG he
  have key : ∀ (u : BraidDistance.SMap) (g : BraidDistance.SMap),
      BraidDistance.Agree 7 (BraidDistance.pull (edgeWires G e.1 e.2) u) g →
      AgreeR 8 3 (restrictR (gadgetZ G e) (posF G.m (ofSMap u))) (posF 7 (ofSMap g)) := by
    intro u g hug X hX
    obtain ⟨hXl, hXinc, hX8⟩ := hX
    match X, hXl, hXinc, hX8 with
    | [i, j, k], _, hXinc, hX8 =>
      simp only [StrictIncr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hXinc
      have hk8 := hX8 k (by simp)
      obtain ⟨⟨hij, hik⟩, hjk, -⟩ := hXinc
      simp only [restrictR, posF, ofSMap, List.map_cons, List.map_nil, gadgetZ]
      by_cases hk : k = 7
      · subst hk
        have h7 : (edgeWires G e.1 e.2 ++ [G.m]).getD 7 0 = G.m := by
          rw [← hlen]; exact gg_getD_end
        rw [h7]
        simp
      · have hk7 : k < 7 := by omega
        obtain ⟨hi1, hi2⟩ := gg_getD_lt (m := G.m) (E := edgeWires G e.1 e.2) (i := i) (by omega)
        obtain ⟨hj1, hj2⟩ := gg_getD_lt (m := G.m) (E := edgeWires G e.1 e.2) (i := j) (by omega)
        obtain ⟨hk1, hk2⟩ := gg_getD_lt (m := G.m) (E := edgeWires G e.1 e.2) (i := k) (by omega)
        have a1 := hlt _ hi2
        have a2 := hlt _ hj2
        have a3 := hlt _ hk2
        rw [hi1, hj1, hk1]
        have n1 : ¬ (G.m ∈ [(edgeWires G e.1 e.2).getD i 0, (edgeWires G e.1 e.2).getD j 0,
            (edgeWires G e.1 e.2).getD k 0]) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
        have n2 : ¬ (7 ∈ [i, j, k]) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
        simp only [n1, n2, ite_false]
        exact hug i j k hij hjk hk7
  exact ⟨key _ _ hs, key _ _ hv⟩

/-- The image of a basis of `[8]` under the relabelling by `gadgetZ G e` lies inside `A_e ∪ {∞}`. -/
theorem restrict_inGadget (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) {X : List Nat}
    (hX : IsRSet 8 3 X) : InGadget G e (X.map fun i => (gadgetZ G e).getD i 0) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi8 := hX.2.2 i hi
  have hlen := (gadgetZ_spec G hG he).2.1
  have hil : i < (gadgetZ G e).length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
  exact List.getElem_mem hil

theorem bigT_valid (G : Graph) (hG : G.Valid) {u : Nat} (hu : u < G.n) :
    ∀ B ∈ bigT G u, IsRSet (G.m + 1) 3 B := by
  have hb := gg_fw_bound G hG hu
  intro B hB
  simp only [bigT, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl <;>
  · refine ⟨rfl, ?_, ?_⟩
    · simp [StrictIncr] <;> omega
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega

/-- The sets `𝒯_u` are pairwise disjoint. -/
theorem bigT_disjoint (G : Graph) (hG : G.Valid) {u w : Nat} (hu : u < G.n) (hw : w < G.n) {B : List Nat}
    (h₁ : B ∈ bigT G u) (h₂ : B ∈ bigT G w) : u = w := by
  obtain ⟨x, B', rfl, hx⟩ := gg_bigT_head G h₁
  obtain ⟨y, B'', hyB, hy⟩ := gg_bigT_head G h₂
  injection hyB with hxy
  subst hxy
  have := gg_owner G (gg_X_mem G hG hu) (gg_X_mem G hG hw) hx hy
  injection this

/-- Only `𝒯_u` and `𝒯_w` contain bases inside `A_e ∪ {∞}`, for `e = uw`. -/
theorem bigT_inGadget (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) {B : List Nat}
    (hB : InGadget G e B) {x : Nat} (hx : x < G.n) (hBx : B ∈ bigT G x) : x = e.1 ∨ x = e.2 := by
  obtain ⟨y, B', rfl, hy⟩ := gg_bigT_head G hBx
  have hyz : y ∈ gadgetZ G e := hB y (by simp)
  have hym := BraidDistance.wiresOf_lt G hG (gg_X_mem G hG hx) y hy
  obtain ⟨e1, e2, e3⟩ := gg_edge_mem G hG he
  have hxo := gg_X_mem G hG hx
  simp only [gadgetZ, edgeWires, List.mem_append, List.mem_singleton] at hyz
  rcases hyz with ((h | h) | h) | h
  · have := gg_owner G hxo e1 hy h; injection this with q; exact Or.inl q
  · have := gg_owner G hxo e2 hy h; cases this
  · have := gg_owner G hxo e3 hy h; injection this with q; exact Or.inr q
  · omega

/-- A basis inside `A_e ∪ {∞}` and `A_f ∪ {∞}` for distinct edges lies in some `𝒯_u`. -/
theorem gadget_overlap (G : Graph) (hG : G.Valid) {e f : Nat × Nat} (he : e ∈ G.edges) (hf : f ∈ G.edges)
    (hef : e ≠ f) {B : List Nat} (hB : IsRSet (G.m + 1) 3 B) (h₁ : InGadget G e B) (h₂ : InGadget G f B) :
    ∃ u, u < G.n ∧ B ∈ bigT G u := by
  have hve := hG.2 _ he
  have hvf := hG.2 _ hf
  -- each element of `B` is `∞` or a wire of the block of a common endpoint
  have elt : ∀ x ∈ B, x = G.m ∨
      ∃ c, (c = e.1 ∨ c = e.2) ∧ (c = f.1 ∨ c = f.2) ∧ x ∈ BraidDistance.wiresOf G (.X c) := by
    intro x hx
    have hxe := h₁ x hx
    have hxf := h₂ x hx
    simp only [gadgetZ, List.mem_append, List.mem_singleton] at hxe hxf
    rcases hxe with hxe | hxe
    · rcases hxf with hxf | hxf
      · exact Or.inr (gg_common G hG he hf hef x hxe hxf)
      · exact Or.inl hxf
    · exact Or.inl hxe
  -- at most one common endpoint
  have uniq : ∀ c d, (c = e.1 ∨ c = e.2) → (c = f.1 ∨ c = f.2) → (d = e.1 ∨ d = e.2) →
      (d = f.1 ∨ d = f.2) → c = d := by
    intro c d hc1 hc2 hd1 hd2
    by_cases hcd : c = d
    · exact hcd
    · exfalso
      apply hef
      have q1 : e.1 = f.1 := by omega
      have q2 : e.2 = f.2 := by omega
      exact Prod.ext q1 q2
  obtain ⟨hBl, hBinc, hBm⟩ := hB
  match B, hBl, hBinc, hBm, elt with
  | [a, b, c], _, hBinc, hBm, elt =>
    simp only [StrictIncr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hBinc
    obtain ⟨⟨hab, hac⟩, hbc, -⟩ := hBinc
    have hcm := hBm c (by simp)
    rcases elt a (by simp) with ha | ⟨ca, ha1, ha2, ha⟩
    · omega
    rcases elt b (by simp) with hb | ⟨cb, hb1, hb2, hb⟩
    · omega
    have qab := uniq ca cb ha1 ha2 hb1 hb2
    subst qab
    have hcan : ca < G.n := by omega
    refine ⟨ca, hcan, ?_⟩
    simp only [gg_wiresOf_X, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases elt c (by simp) with hc | ⟨cc, hc1, hc2, hc⟩
    · subst hc
      simp only [bigT, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq, and_true]
      omega
    · have qac := uniq ca cc ha1 ha2 hc1 hc2
      subst qac
      simp only [gg_wiresOf_X, List.mem_cons, List.not_mem_nil, or_false] at hc
      simp only [bigT, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq, and_true]
      omega

end OMDistance
