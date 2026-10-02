import BraidDistance.Words
import BraidDistance.Certificates

/-!
# Algebra of sequences of commutations and braid moves

Paths compose, reverse, survive a context `A ++ · ++ C` and a shift of all letters (Lemma 2.7, first part:
a sequence on the positions `q, …, q+k-1` lifts to any word containing it), blocks of letters that pairwise
commute can be exchanged by commutations, turning a bead over is one braid move (property (B) of Section 3),
and a successful certificate check yields a path.
-/

namespace BraidDistance

theorem Path.single {w w' : List Nat} {k : Nat} (h : Step w w' k) : Path w w' k := by
  simpa using Path.cons h (Path.refl w')

theorem Path.cast {w w' : List Nat} {k k' : Nat} (h : Path w w' k) (hk : k = k') : Path w w' k' :=
  hk ▸ h

theorem Path.trans {w₁ w₂ w₃ : List Nat} {a b : Nat} (h₁ : Path w₁ w₂ a) (h₂ : Path w₂ w₃ b) :
    Path w₁ w₃ (a + b) := by
  induction h₁ with
  | refl w => simpa using h₂
  | cons hs _ ih => exact (Path.cons hs (ih h₂)).cast (by omega)

theorem Step.symm {w w' : List Nat} {k : Nat} (h : Step w w' k) : Step w' w k := by
  cases h with
  | comm A C i j hij => exact Step.comm A C j i (by omega)
  | braidUp A C i => exact Step.braidDown A C i
  | braidDown A C i => exact Step.braidUp A C i

theorem Path.symm {w w' : List Nat} {k : Nat} (h : Path w w' k) : Path w' w k := by
  induction h with
  | refl w => exact Path.refl w
  | cons hs _ ih => exact (Path.trans ih (Path.single hs.symm)).cast (by omega)

theorem Step.context {w w' : List Nat} {k : Nat} (h : Step w w' k) (A C : List Nat) :
    Step (A ++ w ++ C) (A ++ w' ++ C) k := by
  cases h with
  | comm A' C' i j hij =>
    have := Step.comm (A ++ A') (C' ++ C) i j hij
    simpa [List.append_assoc] using this
  | braidUp A' C' i =>
    have := Step.braidUp (A ++ A') (C' ++ C) i
    simpa [List.append_assoc] using this
  | braidDown A' C' i =>
    have := Step.braidDown (A ++ A') (C' ++ C) i
    simpa [List.append_assoc] using this

/-- Lemma 2.7 (lifting), first part: a path inside a context. -/
theorem Path.context {w w' : List Nat} {k : Nat} (h : Path w w' k) (A C : List Nat) :
    Path (A ++ w ++ C) (A ++ w' ++ C) k := by
  induction h with
  | refl w => exact Path.refl _
  | cons hs _ ih => exact Path.cons (hs.context A C) ih

theorem Step.shift {w w' : List Nat} {k : Nat} (h : Step w w' k) (q : Nat) :
    Step (shiftW q w) (shiftW q w') k := by
  cases h with
  | comm A C i j hij =>
    have := Step.comm (shiftW q A) (shiftW q C) (i + q) (j + q) (by omega)
    simpa [shiftW, List.map_append] using this
  | braidUp A C i =>
    have := Step.braidUp (shiftW q A) (shiftW q C) (i + q)
    simpa [shiftW, List.map_append, Nat.add_right_comm] using this
  | braidDown A C i =>
    have := Step.braidDown (shiftW q A) (shiftW q C) (i + q)
    simpa [shiftW, List.map_append, Nat.add_right_comm] using this

/-- A path on the positions `0, …` shifted to the positions `q, …`. -/
theorem Path.shift {w w' : List Nat} {k : Nat} (h : Path w w' k) (q : Nat) :
    Path (shiftW q w) (shiftW q w') k := by
  induction h with
  | refl w => exact Path.refl _
  | cons hs _ ih => exact Path.cons (hs.shift q) ih

/-- A single letter commuting with every letter of a block moves past that block by commutations. -/
private theorem PathLemmas.commute_one (x : Nat) (V : List Nat) (hV : ∀ y ∈ V, x + 2 ≤ y ∨ y + 2 ≤ x)
    (A C : List Nat) : Path (A ++ x :: V ++ C) (A ++ V ++ x :: C) 0 := by
  induction V generalizing A with
  | nil => simpa using Path.refl (A ++ x :: C)
  | cons y V ih =>
    have h1 : Step (A ++ x :: y :: (V ++ C)) (A ++ y :: x :: (V ++ C)) 0 :=
      Step.comm A (V ++ C) x y (hV y (List.mem_cons_self ..))
    have h2 := ih (fun z hz => hV z (List.mem_cons_of_mem _ hz)) (A ++ [y])
    have h3 := Path.cons h1 (by simpa [List.append_assoc] using h2)
    simpa [List.append_assoc] using h3

/-- Two blocks of letters that pairwise commute can be exchanged by commutations. -/
theorem Path.commute (A U V C : List Nat) (h : ∀ x ∈ U, ∀ y ∈ V, x + 2 ≤ y ∨ y + 2 ≤ x) :
    Path (A ++ U ++ V ++ C) (A ++ V ++ U ++ C) 0 := by
  induction U generalizing A with
  | nil => simpa using Path.refl (A ++ V ++ C)
  | cons x U ih =>
    have h1 := ih (A ++ [x]) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have h2 := PathLemmas.commute_one x V (h x (List.mem_cons_self ..)) A (U ++ C)
    have h3 := Path.trans h1 (by simpa [List.append_assoc] using h2)
    simpa [List.append_assoc] using h3

/-- Property (B): turning a bead over is one braid move. -/
theorem Path.bead_flip (A C : List Nat) (q : Nat) :
    Path (A ++ bead false q ++ C) (A ++ bead true q ++ C) 1 := by
  have h := Step.braidUp A C q
  simp only [bead, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append,
    List.append_assoc] at h ⊢
  exact Path.single h

/-- A successful move is a step with the cost of the move. -/
private theorem PathLemmas.applyMv_step {w w' : List Nat} {mv : Mv} (h : applyMv w mv = some w') :
    Step w w' mv.cost := by
  cases mv with
  | c i =>
    simp only [applyMv] at h
    split at h
    · rename_i x y rest hd
      split at h
      · rename_i hxy
        cases h
        have hw' : w = w.take i ++ x :: y :: rest := by
          rw [← hd, List.take_append_drop]
        have := Step.comm (w.take i) rest x y hxy
        rw [← hw'] at this
        simpa [Mv.cost] using this
      · cases h
    · cases h
  | b i =>
    simp only [applyMv] at h
    split at h
    · rename_i x y z rest hd
      split at h
      · rename_i hxyz
        cases h
        obtain ⟨rfl, hy⟩ := hxyz
        have hw' : w = w.take i ++ x :: y :: x :: rest := by
          rw [← hd, List.take_append_drop]
        rcases hy with rfl | rfl
        · have := Step.braidUp (w.take i) rest x
          rw [← hw'] at this
          simpa [Mv.cost] using this
        · have := Step.braidDown (w.take i) rest y
          rw [← hw'] at this
          simpa [Mv.cost] using this
      · cases h
    · cases h

private theorem PathLemmas.runMvs_path : ∀ (ms : List Mv) {w w' : List Nat} {k : Nat},
    runMvs w ms = some (w', k) → Path w w' k
  | [], w, w', k, h => by
    simp only [runMvs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Path.refl w
  | mv :: ms, w, w', k, h => by
    simp only [runMvs] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      split at h
      · cases h
      · rename_i w₂ k₂ h₂
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Path.cons (PathLemmas.applyMv_step h₁) (PathLemmas.runMvs_path ms h₂)

/-- Soundness of the certificate checker. -/
theorem checkCert_sound {w w' : List Nat} {k : Nat} {ms : List Mv} (h : checkCert w w' k ms = true) :
    Path w w' k := by
  unfold checkCert at h
  have h' : runMvs w ms = some (w', k) := by simpa using h
  exact PathLemmas.runMvs_path ms h'

end BraidDistance
