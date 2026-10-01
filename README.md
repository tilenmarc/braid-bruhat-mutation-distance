# Computations for "Computing distances in braid-move graphs, higher Bruhat orders, and oriented-matroid mutation graphs is NP-hard"

This repository contains the programs that accompany the paper

> T. Marc, *Computing distances in braid-move graphs, higher Bruhat orders, and oriented-matroid mutation graphs
> is NP-hard*, 2026.

No proof in the paper depends on a computer. The programs confirm the finite statements used in the proofs.
They also establish a few side remarks that are not used in any proof; these are listed in the section
*Computations* of the paper and marked below. The programs are written directly from the definitions in the
paper and do not reuse any external code.

## Contents

| File | Language | What it does |
|---|---|---|
| `check.py` | Python 3 | Works with sign vectors of words (rank-3 signotopes) and with signotopes and chirotopes of higher rank. Checks Parts I and II of the paper; see the list below. |
| `check_words.py` | Python 3 | The same at the level of reduced words: performs the sequences of braid moves explicitly, comparing commutation classes. Imports `check.py`. |
| `gen_tables.py` | Python 3 | Regenerates the TikZ figures of the paper (`fig_*.tex`) from the definitions. Imports `check.py`. |
| `bm2.c` | C | The higher Bruhat order B(m,2) for m ≤ 8: enumeration, flip graph and breadth-first search. Used for the excess statistics mentioned below. It is not needed for the paper's main results. |
| `outputs/` | text | The outputs of the runs listed below, with timings. |

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
