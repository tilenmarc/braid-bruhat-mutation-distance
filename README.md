# Computations and Lean formalization for "Computing distances in braid-move graphs, higher Bruhat orders, and oriented-matroid mutation graphs is NP-hard"

This repository contains the programs and the Lean formalization that accompany the paper

> T. Marc, *Computing distances in braid-move graphs, higher Bruhat orders, and oriented-matroid mutation graphs
> is NP-hard*, 2026.

No proof in the paper depends on a computer. The programs confirm the finite statements used in the proofs.
They also establish a few side remarks that are not used in any proof; these are listed in the section
*Computations* of the paper and marked below. The programs are written directly from the definitions in the
paper and do not reuse any external code.

In addition, the folder [`lean/`](lean/) contains a complete formal proof of **Theorem 5.4**, the main result of
Part I, in Lean 4 (core Lean only, without Mathlib). The theorem says that the braid-move distance of the two
wiring diagrams of the construction, and the flip distance of their sign vectors in B(m,2), both equal
|D| + 2 VC(G). See [Formal verification in Lean](#formal-verification-in-lean) below.

## Contents

| File | Language | What it does |
|---|---|---|
| `check.py` | Python 3 | Works with sign vectors of words (rank-3 signotopes) and with signotopes and chirotopes of higher rank. Checks Parts I and II of the paper; see the list below. |
| `check_words.py` | Python 3 | The same at the level of reduced words: performs the sequences of braid moves explicitly, comparing commutation classes. Imports `check.py`. |
| `gen_tables.py` | Python 3 | Regenerates the TikZ figures of the paper (`fig_*.tex`) from the definitions. Imports `check.py`. |
| `bm2.c` | C | The higher Bruhat order B(m,2) for m ≤ 8: enumeration, flip graph and breadth-first search. Used for the excess statistics mentioned below. It is not needed for the paper's main results. |
| `outputs/` | text | The outputs of the runs listed below, with timings. |
| `lean/` | Lean 4 | A formal proof of Theorem 5.4; see [`lean/README.md`](lean/README.md). |

## Requirements and usage

The Python scripts need only Python 3.8 or later and its standard library. `bm2.c` needs a C99 compiler.

```sh
python3 check.py          # about 5 minutes, under 100 MB; ends with "ALL CHECKS PASSED"
python3 check_words.py    # about 1 minute; ends with "ALL WORD-LEVEL CHECKS PASSED"
python3 gen_tables.py     # writes fig_*.tex into the current directory

cc -O2 -o bm2 bm2.c
./bm2 bfs 7 0 1           # all pairs of B(7,2) up to symmetry, under a second
./bm2 bfs 8 400 1         # 400 random sources in B(8,2), about 20 seconds
```

The scripts are deterministic: random tests use fixed seeds. The files in `outputs/` were produced by exactly
the code in this repository.

The Lean proof needs [elan](https://github.com/leanprover/elan), which installs the Lean version named in
`lean/lean-toolchain` (4.34.1). No other dependencies are needed.

```sh
cd lean
lake build                                # about 80 seconds; ends with "Build completed successfully"
lake env lean BraidDistance/Axioms.lean   # the axioms used by the main theorem
```

## What is checked

Numbers refer to the paper.

**`check.py`**
- **Four wires (Section 2.4):**
  - the packet cycle of Lemma 2.10, and |B(m,2)| = 2, 8, 62, 908, 24698 for m = 3, …, 7;
  - Lemma 2.2 on random reduced words;
  - the packet criterion (Lemma 2.11), by comparing it with a flip-by-flip replay on random pairs.
- **The gadget (Section 3):**
  - the word κ and properties (K1)–(K3), also asserted by `gen_tables.py` (Figure 2);
  - the sign vectors of the gadget words (Definition 3.1) and the set D_κ (Proposition 3.2(a));
  - the forced cycle of Table 1 (Lemma 3.3);
  - the three orders of Table 2, replayed flip by flip in B(7,2) and checked to be admissible;
  - the four distances of Proposition 3.2(b), 32, 30, 30, 30, by breadth-first search in B(7,2).
- **The construction (Sections 4 and 5):**
  - Lemma 4.5 for the 14 graphs with m ≤ 20;
  - Corollary 4.6 for 27 graphs, among them K5, K3,3, the cube and the Petersen graph;
  - the sequence of Proposition 5.3, replayed flip by flip with length |D| + 2|C|, for every vertex cover of the
    graphs with at most five vertices.
- **The positive fibre and rank three (Sections 6 and 7):** Proposition 6.9 exhaustively for small ground sets,
  and Observation 7.3 for all rank-3 chirotopes on five elements.
- **Higher ranks (Section 8):**
  - Lemmas 8.1, 8.3 and 8.4, by replaying the walks of their proofs, for every flip of every signotope in B(m,2) with
    m ≤ 5, and for 250 signotopes in B(6,2), lifted to ranks 4 and 5;
  - the identity (F_r L s)_Y = F_3 s used in the proof of Proposition 8.5;
  - the two inequalities in the proof of Theorem 8.6, for 4 ≤ r ≤ 8 and a range of m and k.
- **Side remarks (not used in any proof):**
  - the 32-flip sequence of Remark 5.2;
  - the six-wire facts at the end of Section 3: the 16 pairs in B(6,2) with positive excess each have exactly four
    triples whose flip removes the excess, and any two of these share a wire;
  - among the 60 cells with one private wire, κ is the only one with the OR property;
  - the maximal excess 2 in B(6,2).
- **Regression checks:** material from earlier versions of the paper (local sequences, the one-wire lemma, sweeps,
  height certificates).

**`check_words.py`**
- Lemma 2.6 (deleting wires) on random reduced words, including braid moves on triples that meet the kept set in
  two wires.
- Corollary 4.6(a) as a statement about words, for every edge of several graphs.
- The sequence of Proposition 5.3 performed as actual braid moves, with commutation classes compared after every
  factor, for all vertex covers of seven graphs.
- The 32-flip sequence of Remark 5.2 as braid moves.
- *Side remark:* walks of length 17 and 26 from F_3(s_G) to −F_3(v_G) for G = 2K1 and G = K2. These show that
  the hypothesis n ≥ 3 in Theorem 7.2 cannot be dropped.

**`bm2.c`** (*side remarks*, not stated in the paper)
- In B(7,2), the excess d_B − |D| is 0 or 2 for all pairs. The search runs from one vertex of each of the 922 orbits
  of a symmetry group of order 28.
- In B(8,2), pairs with excess 4 exist.

## Formal verification in Lean

The theorem `BraidDistance.main_theorem` in [`lean/BraidDistance/Main.lean`](lean/BraidDistance/Main.lean)
formalizes Theorem 5.4. Take any graph G with vertices 0, …, n−1 and edge set E, and let m = 3n + |E|. Let
`Ws G` and `Wv G` be the words W^s_G and W^v_G of Section 4, s_G and v_G their sign vectors, and |D| the number of
triples on which these differ. The theorem proves:

1. `Ws G` and `Wv G` are reduced words of the longest permutation of S_m.
2. For every vertex cover C, there is a sequence of commutations and braid moves from `Ws G` to `Wv G` with
   exactly |D| + 2|C| braid moves. There is also a walk of length |D| + 2|C| from s_G to v_G in B(m,2).
3. Every such sequence with k braid moves, and every such walk of length k, yields a vertex cover C with
   |D| + 2|C| ≤ k.
4. |D| = 3n(m−3) + 6|E|.

Taking a minimum vertex cover gives d_br([W^s_G], [W^v_G]) = d_B(s_G, v_G) = |D| + 2 VC(G). This is the
corollary `braid_distance_eq`.

**Trust.**
- **Proofs.** The development uses core Lean 4 only, without Mathlib. It contains no `sorry`, no `axiom` and no
  `native_decide`. Finite facts are proved by `decide`, which the Lean kernel evaluates. These include the
  gadget tables (Tables 1 and 2) and the explicit move sequences for the local cases.
- **Axioms.** The main theorem depends only on Lean's standard axioms `propext`, `Classical.choice` and
  `Quot.sound`; `lake env lean BraidDistance/Axioms.lean` prints this.
- **Definitions.** What a reader has to check is that the definitions in the statement match the paper:
  reduced words, sign vectors, commutations and braid moves, signotopes and walks in B(m,2), and vertex covers.
  They take about 250 lines in four files.
- **Construction.** `Sanity.lean` checks by `decide` that the Lean construction reproduces the words and sign
  vectors computed by `check.py`.

**Approach.** The proof avoids the classical correspondence between commutation classes and signotopes
(Theorem 2.8). The upper bound is an explicit sequence of moves, and the lower bound for words goes through
d_B ≤ d_br.

**Not formalized.**
- the polynomial-time computability of the construction, and therefore the NP-hardness statement itself
  (Theorem 5.5);
- Part II of the paper.

[`lean/README.md`](lean/README.md) has the details: the statement, the trusted definitions, the conventions, the
small deviations from the paper's presentation, the proof outline and a map from files to lemmas.

## Data

The two sign vectors of the gadget, in lexicographic order of the triples 123, 124, …, 567:

```
g^s = +++++++++++----++++++-------------+
g^v = +-----------+++-----+++++-+++++++++
```

The 32-flip sequence of Remark 5.2, a shortest sequence from β₁β₅κ to κβ₁β₅ that flips 147 twice and no bead
triple:

```
147 167 157 156 247 267 257 256 467 367 457 357 347 456 245 145
356 235 135 125 346 234 134 124 236 136 126 146 237 137 127 147
```

## License

MIT; see `LICENSE`.
