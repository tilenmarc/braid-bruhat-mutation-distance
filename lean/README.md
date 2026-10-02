# Lean formalization of Theorem 5.4

This folder contains a complete formal proof, in Lean 4, of Theorem 5.4 of the paper. Theorem 5.4 is the main
result of Part I. For every graph G with n vertices and edge set E, the construction of Section 4 gives two
wiring diagrams W^s_G and W^v_G on m = 3n + |E| wires. Both of the following distances equal
|D| + 2 VC(G), where |D| = 3n(m−3) + 6|E|:

- the braid-move distance between the two diagrams;
- the flip distance in B(m,2) between their sign vectors.

- **Core Lean only.** The library uses Lean 4.34.1 and no other dependencies: no Mathlib and no Batteries.
- **No unfinished proofs.** There is no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe`.
- **Finite facts by kernel evaluation.** These include the gadget tables and the local move sequences. They are
  proved by `decide`, which the Lean kernel evaluates.
- **Standard axioms only.** The main theorem depends only on Lean's three standard axioms.

Theorem numbers refer to the version of the paper dated 1 October 2026.

## Building and checking

Install [elan](https://github.com/leanprover/elan). It downloads the Lean version named in `lean-toolchain`
automatically. Then run:

```sh
cd lean
lake build                                # about 80 seconds from scratch
lake env lean BraidDistance/Axioms.lean   # prints the axioms of the main theorem
```

The build ends with `Build completed successfully` and gives no warnings. The axiom check prints:

```
'BraidDistance.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidDistance.braid_distance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BraidDistance.exists_min_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
```

If any proof were incomplete, or used `native_decide`, this list would also contain `sorryAx` or
`Lean.ofReduceBool`.

## The statement

`BraidDistance/Main.lean`:

```lean
theorem main_theorem (G : Graph) (hG : G.Valid) :
    Reduced G.m (Ws G) ∧ Reduced G.m (Wv G) ∧
    (∀ C : List Nat, IsVertexCover G C →
      Path (Ws G) (Wv G)
        (hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length)) ∧
    (∀ C : List Nat, IsVertexCover G C →
      Walk G.m (signVec G.m (Ws G)) (signVec G.m (Wv G))
        (hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length)) ∧
    (∀ k : Nat, Path (Ws G) (Wv G) k → ∃ C : List Nat, IsVertexCover G C ∧
      hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length ≤ k) ∧
    (∀ k : Nat, Walk G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) k → ∃ C : List Nat,
      IsVertexCover G C ∧ hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length ≤ k) ∧
    hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) = 3 * G.n * (G.m - 3) + 6 * G.edges.length
```

Write s_G and v_G for the two sign vectors and |D| for their Hamming distance. For every valid graph G, the
theorem says:
1. `Ws G` and `Wv G` are reduced words of the longest permutation w₀ ∈ S_m.
2. For every vertex cover C, there is a sequence of commutations and braid moves from `Ws G` to `Wv G` with
   exactly |D| + 2|C| braid moves.
3. For every vertex cover C, there is a walk of length |D| + 2|C| from s_G to v_G in B(m,2).
4. Every sequence of moves with k braid moves yields a vertex cover C with |D| + 2|C| ≤ k.
5. Every walk of length k from s_G to v_G yields a vertex cover C with |D| + 2|C| ≤ k.
6. |D| = 3n(m−3) + 6|E|.

The statement has no minima, so Lean needs no notion of distance. The braid-move distance d_br is the least k
with `Path (Ws G) (Wv G) k`, and the flip distance d_B is the least k with `Walk m s_G v_G k`.

Take C to be a minimum vertex cover. Then (2)–(5) give d_br = d_B = |D| + 2 VC(G). This is stated in Lean as
`braid_distance_eq`, and `exists_min_cover` shows that a minimum cover exists.

## What has to be trusted

Apart from the Lean kernel, a reader has to check that the definitions in the statement mean what the paper
says. They are short and are collected in four files:

| File | Defines | Paper |
|---|---|---|
| `Basic.lean` | triples a < b < c < m, sign maps (`true` is +), flips, the difference set `diffList` (D(u,v)), its size `hamming` | Section 2.1 |
| `Words.lean` | words as lists of letters, the swaps of a word, `Reduced` (every pair of wires swapped exactly once), the sign vector `signVec` (+ if and only if ⟨ab⟩ precedes ⟨bc⟩), `Step` (a commutation costs 0, a braid move costs 1), `Path` | Definition 2.1 |
| `Signotope.lean` | packets, `IsSignotope` (every packet changes sign at most once), `Walk` (a walk in B(m,2)) | Section 2.2 |
| `Graph.lean` | graphs on the vertices 0, …, n−1 with an edge list, `Valid`, `IsVertexCover` (a list of vertices without repetitions that meets every edge) | Section 4 |

These four files fix the meaning of "braid-move distance", "flip distance in B(m,2)" and "vertex cover".

The words `Ws G` and `Wv G` are defined in three further files: `Gadget.lean`, `Cases.lean` and
`Construction.lean`. They follow Sections 3 and 4, and they matter only for recognizing the words as those of
the paper. The theorem itself, |D| + 2 VC(G) for both distances, holds for the words as defined in Lean, whatever
one makes of the definitions.

`Sanity.lean` checks by `decide` that these definitions agree with the paper and with `../check.py`:
- the word, the sign vectors, the shadow sweep and |D| = 84 for the path P_3 (Example 4.7);
- the set D_κ of Table 2 and the two gadget sign vectors;
- the values of |D| for 2K_1 and K_3.

The certificates in `Certificates.lean` (sequences of moves) are data, not trusted code. A checker proved
correct in Lean (`checkCert_sound`) turns each certificate into a `Path`.

**Not formalized.** The following parts of the paper are not covered:
- the polynomial-time computability of the construction, and therefore the NP-hardness statement itself
  (Theorem 5.5);
- the reformulations of Corollary 5.6;
- Part II of the paper: oriented matroids and higher Bruhat orders.

The proof does not need Theorem 2.8, the correspondence between commutation classes and signotopes.

## Conventions and deviations from the paper

**Conventions.**
- **Labels.** Everything is 0-based: wires, vertices and positions start at 0, and the letter `i` is the
  paper's σ_{i+1}. The gadget wires 1, …, 7 are 0, …, 6.
- **Sign maps.** A sign map is a function `Nat → Nat → Nat → Bool`. Only its values on valid triples
  a < b < c < m matter.

**Deviations from the paper.** None of them changes the theorem:
- **Bead order.** The beads in the words are listed by increasing vertex. The paper notes that their order does
  not matter up to commutations, while `check.py` lists them by position. So `Wv G` agrees with the word of
  `check.py` only up to commuting beads; its sign vector is the same.
- **Shadow sweep.** The sweep is written out explicitly, using the arrangements of Lemma 4.1(b). It ends with the
  completion that the paper fixes "for definiteness".
- **Local cases.** The sign facts of Lemma 4.5 are proved by `decide` on the local words, not by Lemma 2.2(d).
- **Lemma 3.3** is proved for walks of signotopes. The version for words follows through Lemma 2.4.
- **A cell with two beads of type β** gets its own certificate of cost 32. This makes the one-step lemma hold for
  every choice of bead types.

## How the proof goes

The proof follows Part I of the paper and avoids Theorem 2.8 by the chain

    |D| + 2 VC(G)  ≤  d_B(s_G, v_G)  ≤  d_br([W^s_G], [W^v_G])  ≤  |D| + 2 VC(G).

- **Upper bound.** The move sequences of Proposition 5.3 are constructed explicitly:
  - the local move sequences of Lemma 4.5(b) and Table 2 are certificates checked by `decide`;
  - Lemma 2.7 lifts them into the whole word;
  - the decomposition of Lemma 4.5(a) places each one in its window;
  - the bead turns (property (B) of Section 3) add the cost 2|C|.
- **Middle inequality.** A braid move flips exactly one triple (Lemma 2.4), so a sequence of moves gives a walk
  in B(m,2) of the same length (`path_to_walk`).
- **Lower bound.** This is Proposition 5.1, and it combines four ingredients:
  - parity (Lemma 2.5);
  - restriction of walks to the seven wires of a gadget (Lemma 2.6);
  - the gadget lower bound, proved from Table 1 and the packet cycle of Lemma 2.10 by `decide`;
  - the vertex-cover charging argument.

## Files

| File | Content |
|---|---|
| `Basic.lean`, `Words.lean`, `Signotope.lean`, `Graph.lean` | Definitions in the statement (see above) |
| `Gadget.lean`, `Cases.lean`, `Construction.lean` | κ, beads, the gadget words, the local cases of Lemma 4.5, the construction of Section 4 |
| `Certificates.lean` | Move certificates for the local cases, generated by `scripts/gen_certs.py` |
| `BasicLemmas.lean`, `PathLemmas.lean`, `Arrangement.lean` | General facts about sign maps, sequences of moves (Lemma 2.7) and arrangements |
| `SignVector.lean`, `LocalReplace.lean`, `BraidFlip.lean` | Lemmas 2.2, 2.3 and 2.4, and `path_to_walk` |
| `HammingParity.lean`, `Restrict.lean`, `Packets.lean` | Lemmas 2.5, 2.6 and 2.10 |
| `GadgetLower.lean`, `LocalCases.lean` | Lemma 3.3 (Table 1); Proposition 3.2(a), (K1)–(K3), Lemma 4.5(b) and Table 2 |
| `ConstructionBasic.lean`, `Wires.lean` | Unfolding the construction; the wire labels of Section 4.1 |
| `Sweep.lean`, `SweepPairs.lean`, `SweepCount.lean` | Lemmas 4.1 and 4.2, and the count in Corollary 4.6(b) |
| `FactorOverlap.lean`, `Blowup.lean`, `StepDecomp.lean`, `BeadFlip.lean`, `StepLemma.lean`, `Chain.lean` | Lemmas 4.4 and 4.5, and Corollary 4.6 |
| `Charging.lean`, `LowerBound.lean`, `UpperBound.lean` | Propositions 5.1 and 5.3 |
| `Main.lean` | Theorem 5.4 (`main_theorem`, `braid_distance_eq`, `exists_min_cover`) |
| `Sanity.lean` | Checks of the definitions against the paper and `check.py` |
| `Axioms.lean` | The axiom check; it is not part of the default build target |

The library has about 7,500 lines. The modules that take longest to build are `Sanity.lean`, `BraidFlip.lean` and
`LocalCases.lean`. Most of their time goes to kernel evaluation of `decide`.

## Scripts

Both scripts need Python 3 only.

- `scripts/gen_certs.py` finds the local move certificates and replays them. With `--write`, it regenerates
  `BraidDistance/Certificates.lean`; the output is identical to the file in this repository.
- `scripts/ref_values.py` prints the reference values from `../check.py` in 0-based labels. These are the values
  used in `Sanity.lean`.
