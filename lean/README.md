# Lean formalization

This folder contains complete formal proofs, in Lean 4, of the main results of both parts of the paper. There are
two libraries:

- **`BraidDistance`** (Part I) proves **Theorem 5.4**. For every graph G with n vertices and edge set E, the
  construction of Section 4 gives two wiring diagrams W^s_G and W^v_G on m = 3n + |E| wires. Both of the following
  equal |D| + 2 VC(G), where |D| = 3n(m−3) + 6|E|:
  - the braid-move distance between the two diagrams;
  - the flip distance in B(m,2) between their sign vectors.
- **`OMDistance`** (Part II) proves the results on oriented matroids and higher Bruhat orders:
  - **Theorem 7.2**: the same distance |D| + 2 VC(G) for walks of chirotopes and, for n ≥ 3, in the mutation graph
    of rank 3;
  - **Proposition 8.5**: excess amplification by the lift;
  - **Theorem 8.6** and **Corollary 8.7**, without the complexity statements: the equivalences "distance ≤ K if
    and only if VC(G) ≤ k" for the lifted instances, in the mutation graph of every rank r ≥ 4 and in the higher
    Bruhat order B(n, r−1).

Common properties of both libraries:
- **Core Lean only.** They use Lean 4.34.1 and nothing else: no Mathlib, no Batteries, no other dependencies.
  Finite sets and binomial coefficients are defined in the library itself.
- **No unfinished proofs.** There is no `sorry`, `axiom`, `native_decide`, `bv_decide`, `implemented_by`, `extern`
  or `unsafe`.
- **Finite facts by kernel evaluation.** Examples are the gadget tables, the local move sequences and the 64 cases
  of the four-point check. They are proved by `decide`, which the Lean kernel evaluates.
- **Standard axioms only.** Every main theorem depends only on Lean's three standard axioms.

Theorem numbers refer to the version of the paper dated 1 October 2026.

## Building and checking

Install [elan](https://github.com/leanprover/elan). It downloads the Lean version named in `lean-toolchain`
automatically. Then run:

```sh
cd lean
lake build                                # both libraries, about 1-2 minutes from scratch
lake env lean BraidDistance/Axioms.lean   # axioms of the main theorems of Part I
lake env lean OMDistance/Axioms.lean      # axioms of the main theorems of Part II
```

The build ends with `Build completed successfully` and gives no warnings. Every line printed by the two axiom
checks reads

```
'<theorem>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

If any proof were incomplete, or used `native_decide`, the list would also contain `sorryAx` or
`Lean.ofReduceBool`.

# Part I: Theorem 5.4 (`BraidDistance`)

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

**Not formalized in Part I.** The following parts are not covered:
- the polynomial-time computability of the construction, and therefore the NP-hardness statement itself
  (Theorem 5.5);
- the reformulations of Corollary 5.6.

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

# Part II: oriented matroids and higher Bruhat orders (`OMDistance`)

`OMDistance` imports `BraidDistance` and reuses Theorem 5.4, the gadget lower bound (Lemma 3.3) and the charging
argument. It has about 6,000 lines in 41 files.

## The statements

All statements are again stated without minima.

**`rank3_theorem`** (Theorem 7.2, `OMDistance/MainRank3.lean`). Let G be a valid graph with n ≥ 1 vertices, and
put χ_s = Pos₃(s_G) and χ_v = Pos₃(v_G) on [m] ∪ {∞} = {0, …, m}, with ∞ = m. Then:
1. χ_s and χ_v are uniform chirotopes of rank 3.
2. For every vertex cover C, there is a walk of chirotopes of length |D| + 2|C| from χ_s to χ_v. There is also a
   walk of that length in the mutation graph.
3. Every walk of chirotopes of length k from χ_s to χ_v yields a vertex cover C with |D| + 2|C| ≤ k.
4. If n ≥ 3, the same holds for every walk of length k in the mutation graph from [χ_s] to [χ_v].
5. |D| = 3n(m−3) + 6|E|.

`rank3_distance_eq` turns this into d̃(χ_s, χ_v) = |D| + 2 VC(G), and, for n ≥ 3, into
d([χ_s], [χ_v]) = |D| + 2 VC(G).

**`prop_excess`** (Proposition 8.5, `OMDistance/Excess.lean`). Let s, t be rank-3 signotopes on [m] with m ≥ 3,
let r ≥ 4 and q = r − 3, and lift with c ≥ q new elements. Put:
- h = |D(s,t)| and H = |D(L s, L t)|;
- λ = binom(c, q) and μ = binom(c+m−3, q).

Then:
1. L s and L t are signotopes of rank r.
2. Every walk of chirotopes of length ℓ from Pos_r(L s) to Pos_r(L t) yields a walk of chirotopes of length k from
   Pos₃(s) to Pos₃(t) with λk + H ≤ ℓ + λh.
3. Every walk in B(N∪S, r−1) from L s to L t is a walk of chirotopes between their positive fibres.
4. Every walk of length k in B(m,2) from s to t yields a walk of length ℓ in B(N∪S, r−1) from L s to L t with
   ℓ + μh ≤ H + μk.

**`higher_rank_theorem`** (`OMDistance/MainHigher.lean`). For the instances s = s_G and t = v_G, it gives the
chain of the proof of Theorem 8.6:
- for every vertex cover C, a walk of length at most H + 2μ|C|, both in B(N∪S, r−1) and of chirotopes;
- every walk of length ℓ of either kind yields a vertex cover C with H + 2λ|C| ≤ ℓ.

**The three reductions** (`OMDistance/MainHigher.lean`). Let n ≥ 2, k ≥ 1, c = q·m·(k+1) + q and
K = H + 2μk. Then a walk of length at most K exists if and only if G has a vertex cover with at most k vertices.
There is one version for each kind of walk:
- `hbo_reduction` (Corollary 8.7): walks in the higher Bruhat order B(N∪S, r−1), between the lifts;
- `chiro_reduction`: walks of chirotopes, between their positive fibres;
- `allranks_reduction` (Theorem 8.6): walks in the mutation graph of rank r. This version also assumes k ≤ n, as
  the paper does.

```lean
theorem allranks_reduction (G : Graph) (hG : G.Valid) (hn : 2 ≤ G.n) {r k c : Nat} (hr : 4 ≤ r) (hk : 1 ≤ k)
    (hkn : k ≤ G.n) (hcdef : c = (r - 3) * G.m * (k + 1) + (r - 3)) :
    (∃ ℓ, ℓ ≤ hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom (c + G.m - 3) (r - 3) * k ∧
        OMWalk (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G))) (posF (c + G.m) (lift c (vMap G))) ℓ) ↔
      ∃ C, IsVertexCover G C ∧ C.length ≤ k
```

The supporting results of Sections 6–8 are also stated and proved:
- Observation 6.3, Lemma 6.5 (the parts that are needed) and Lemma 6.6;
- Proposition 6.9 (`fibre`, both directions, every rank r ≥ 2) and Lemma 6.10 (`sheet_a`, `sheet_b`);
- Proposition 7.1 (`prop_lower`);
- Lemma 8.1 (`onestep_a`, `onestep_b`), Lemma 8.3 and Lemma 8.4 (`liftflip`).

## What has to be trusted

In addition to the Part I definitions above (graphs, vertex covers, s_G, v_G and |D|), five short files:

| File | Defines | Paper |
|---|---|---|
| `OMDistance/Basic.lean` | r-subsets of [M] as increasing lists, with a proved enumeration `rsets`; sign maps `List Nat → Bool`; flips, D(u,v) and the Hamming distance; walks in a graph of sign maps; binomial coefficients by Pascal's rule | Section 6 |
| `OMDistance/Chirotope.lean` | the extension to ordered tuples by the sign of the sorting permutation (counted by inversions); (GP); `IsChirotope` (uniform chirotopes, Definition 6.1); `ChiroWalk`; `OMWalk` (walks in the mutation graph, Definition 6.2) | Section 6.1 |
| `OMDistance/Signotope.lean` | packets in lexicographic order; `IsSignotopeR` (signotopes of rank r, Definition 6.8); `SigWalk` (walks in B([M], r−1)); the positive fibre `posF`, with ∞ above all other elements | Sections 6.2, 6.3 |
| `OMDistance/Lift.lean` | the lift of Definition 8.2, with N = {0, …, c−1} below S = {c, …, c+m−1} below ∞ = c+m; the map v ↦ v′ of Lemma 8.1 | Section 8 |
| `OMDistance/Instances.lean` | s_G and v_G of Part I, viewed as rank-3 sign maps | Sections 7, 8 |

- **`IsChirotope`** is literally Definition 6.1. The equivalent form of (GP) on sets, which the proofs use, is a
  proved lemma (`isChirotope_iff_set`).
- **`OMWalk`** describes a walk in the mutation graph by representatives χ₀, …, χ_k:
  - every χ_i is a uniform chirotope;
  - for each i, χ_{i+1} or −χ_{i+1} differs from χ_i in exactly one basis;
  - χ_k agrees with ψ or with −ψ.

  So it is a walk between the oriented matroids [χ] = {χ, −χ} of Definition 6.2.

`OMDistance/Sanity.lean` checks the definitions by `decide` against the paper and `../check.py`:
- **Counts.** The numbers of uniform chirotopes match: 48, 16, 384 and 32 for (rank, elements) = (2,4), (3,4),
  (3,5) and (4,5). The numbers of signotopes match on small ground sets.
- **Proposition 6.9** holds on all maps of ranks 2 and 3 on four elements.
- **The gadget.** Pos₃(g^s) and Pos₃(g^v) are chirotopes at Hamming distance 30. Flipping the basis {0,1,∞} is a
  mutation, while flipping {0,2,∞} violates (GP).
- **A small lift** is a signotope with the predicted Hamming distance 58.

## Deviations from the paper and what is not formalized

**Deviations.**
- **Hypothesis n ≥ 1.** Theorem 7.2 and `higher_rank_theorem` assume n ≥ 1. For the empty graph the ground set
  {∞} has no bases, and Definition 6.1 requires r ≤ |Ω|.
- **Hypothesis m ≥ 3.** Proposition 8.5 assumes m ≥ 3.
- **Two stronger equivalences.** `hbo_reduction` and `chiro_reduction` do not need the hypothesis k ≤ n.
- **Lemma 6.6** is formalized as pulling walks back along an injective relabelling of bases. This one mechanism
  covers both the restriction to A_e ∪ {∞} and the minors χ_Y of Proposition 8.5.
- **Contraction** is formalized only at the minimum element, which is the only case the proofs use.

**Not formalized.**
- Section 7.1: the normal form, realizability and the rank-3 diameter bound (Observations 7.3 and 7.5, Lemma 7.4,
  Proposition 7.6);
- duality (Lemma 6.7) and the statements about corank;
- reorientation and relabelling in Lemma 6.5;
- all complexity statements: NP membership, polynomial-time computability, and Theorems 7.7 and 8.6 and
  Corollary 8.7 as complexity statements (their reductions are formalized, see above).

## How the proof goes

- **Chirotopes.**
  - In (GP) the signs of the sorting permutations cancel, so (GP) can be checked on sets (`isChirotope_iff_set`).
  - Every signotope is a chirotope (`signotope_isChirotope`). Fix σ and a < b < c < d outside it. The six values
    u(σ ∪ {x,y}) form a rank-2 signotope on the four points a, b, c, d, and (GP) for them is a 64-case check by
    `decide`.
  - Proposition 6.9 and Lemma 6.10 follow.
- **Rank 3.**
  - **Upper bound:** the walks of Part I, mapped by Pos₃.
  - **Lower bound (Proposition 7.1):**
    - restrict a walk to A_e ∪ {∞};
    - a walk without extra flips there would, by Lemma 6.10(a), be a walk of length 30 in B(7,2), which Part I's
      Lemma 3.3 excludes;
    - a charging argument with the four bases inside X_u ∪ {∞} gives the vertex cover;
    - parity gives the bound.
  - **Mutation graph:** for n ≥ 3, Observation 6.3 and a count show that −Pos₃(v_G) is too far away.
- **Higher ranks.**
  - Lemma 8.1(b) (`onestep_b`) uses the early/late ordering of the paper. Lemma 8.4 follows by induction on r.
  - **Proposition 8.5, upper bound:** replace every flip by the walk of Lemma 8.4.
  - **Proposition 8.5, lower bound:**
    - for each q-set Y of new elements, the minor χ_Y (contract Y, delete the other new elements) turns a walk into
      a walk on S ∪ {∞};
    - choosing Y with the fewest flips and counting the remaining flips by parity gives the bound.
  - **The reductions** need two arithmetic facts: μ/λ < (k+1)/k (`ArithRatio.lean`), and the count showing that
    −Pos_r(L v_G) is far (`ArithFar.lean`).

## Files

| Files (in `OMDistance/`) | Content |
|---|---|
| `Basic.lean`, `Chirotope.lean`, `Signotope.lean`, `Lift.lean`, `Instances.lean` | Trusted definitions (see above) |
| `RSets.lean`, `Sorting.lean`, `Binom.lean`, `SignMapLemmas.lean` | Finite sets as increasing lists, insertion sort and inversions, binomial coefficients, sign maps |
| `Parity.lean`, `WalkLemmas.lean`, `Pullback.lean` | Lemma 2.5 for every rank, walks as lists of flips, pulling walks back (Lemma 6.6) |
| `ChiroSetForm.lean`, `ChiroBasic.lean`, `ObsCover.lean`, `Minors.lean` | The set form of (GP), Observation 6.3, Lemma 6.5 |
| `SignotopeBasic.lean`, `SigChiro.lean`, `Fibre.lean`, `Sheet.lean`, `Bridge3.lean` | Signotopes are chirotopes, Proposition 6.9, Lemma 6.10, the bridge to Part I |
| `GadgetChiro.lean`, `GadgetGeometry.lean`, `ChargingT.lean`, `LowerRank3.lean`, `ArithRank3.lean` | Proposition 7.1 and the count for the mutation graph |
| `MainRank3.lean` | Theorem 7.2 (`rank3_theorem`, `rank3_distance_eq`) |
| `OneStep.lean`, `OneStepWalk.lean`, `LiftBasic.lean`, `LiftHamming.lean`, `LiftFlip.lean` | Lemmas 8.1, 8.3 and 8.4, and the Hamming distance of lifts |
| `ExcessUpper.lean`, `MinorLift.lean`, `ExcessLower.lean`, `Excess.lean` | Proposition 8.5 (`prop_excess`) |
| `ArithRatio.lean`, `ArithFar.lean`, `MainHigher.lean` | Theorem 8.6 and Corollary 8.7 (`higher_rank_theorem` and the three reductions) |
| `Sanity.lean` | Checks of the definitions against the paper and `check.py` |
| `Axioms.lean` | The axiom check; it is not part of the default build target |

# Scripts

Both scripts need Python 3 only.

- `scripts/gen_certs.py` finds the local move certificates of Part I and replays them. With `--write`, it
  regenerates `BraidDistance/Certificates.lean`; the output is identical to the file in this repository.
- `scripts/ref_values.py` prints the reference values from `../check.py` in 0-based labels. These are the values
  used in `BraidDistance/Sanity.lean`.
