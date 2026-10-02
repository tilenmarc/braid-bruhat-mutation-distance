"""Generate explicit commutation/braid-move certificates for the local factor cases (Lemma 4.5, Table 2).

Every word is 0-based: the letter i exchanges positions i and i+1.  A certificate is a list of moves
  ('c', i): commutation of the letters at indices i, i+1 (they must differ by at least 2),
  ('b', i): braid move on the letters at indices i, i+1, i+2 (pattern x, x+-1, x).
The moves are found from a flip order: for each triple, the word is reordered by commutations (bubble sort to
a linear extension of the heap order) so that the three letters of the triple are consecutive, and then the braid
move is applied.  Every certificate is replayed and checked here and again in Lean by `decide`.

Usage: python3 gen_certs.py [--write]   (--write regenerates ../BraidDistance/Certificates.lean)
"""
import itertools
C = itertools.combinations

KAPPA = [3, 2, 1, 0, 3, 2, 4, 3, 2, 1, 5, 4, 3, 2, 3]


def bead(t, q):
    return [q + 1, q, q + 1] if t else [q, q + 1, q]


def move_word(a, b):
    return [i + j for j in range(b) for i in reversed(range(a))]


def swaps(word, m):
    pos = list(range(m)); out = []
    for i in word:
        a, b = pos[i], pos[i + 1]
        out.append((min(a, b), max(a, b)))
        pos[i], pos[i + 1] = b, a
    return out


def sig(word, m):
    sw = swaps(word, m)
    assert len(set(sw)) == len(sw) == m * (m - 1) // 2, "not reduced"
    t = {p: k for k, p in enumerate(sw)}
    return {(a, b, c): t[(a, b)] < t[(b, c)] for a, b, c in C(range(m), 3)}


def heap_less(word):
    n = len(word); less = [set() for _ in range(n)]
    for j in range(n):
        for i in range(j):
            if abs(word[i] - word[j]) <= 1:
                less[j].add(i); less[j] |= less[i]
    return less


def bubble(word, target_perm, moves):
    """Reorder `word` so that its letters appear in the order of the index list target_perm, by adjacent
    commutations; returns the new word.  target_perm is a linear extension of the heap order."""
    cur = list(range(len(word)))          # cur[k] = original index of the letter now at k
    rank = {idx: r for r, idx in enumerate(target_perm)}
    w = list(word)
    changed = True
    while changed:
        changed = False
        for k in range(len(w) - 1):
            if rank[cur[k]] > rank[cur[k + 1]]:
                assert abs(w[k] - w[k + 1]) >= 2
                w[k], w[k + 1] = w[k + 1], w[k]
                cur[k], cur[k + 1] = cur[k + 1], cur[k]
                moves.append(('c', k))
                changed = True
    return w


def braid_flip(word, m, T, moves):
    sw = swaps(word, m)
    ids = [k for k, p in enumerate(sw) if set(p) <= set(T)]
    assert len(ids) == 3
    i1, i2, i3 = ids
    less = heap_less(word)
    for x in range(len(word)):
        if x not in ids and i1 in less[x] and x in less[i3]:
            return None
    up = {x for x in range(len(word)) if i1 in less[x]} | {i1}
    first = [x for x in range(len(word)) if x not in up]
    rest = [x for x in range(len(word)) if x in up and x not in ids]
    target = first + [i1, i2, i3] + rest
    w = bubble(word, target, moves)
    k = len(first)
    a, b, c = w[k:k + 3]
    assert a == c and abs(a - b) == 1
    w[k:k + 3] = [b, a, b]
    moves.append(('b', k))
    return w


def replay(word, moves):
    w = list(word); nb = 0
    for kind, i in moves:
        if kind == 'c':
            assert abs(w[i] - w[i + 1]) >= 2
            w[i], w[i + 1] = w[i + 1], w[i]
        else:
            assert w[i] == w[i + 2] and abs(w[i] - w[i + 1]) == 1
            w[i], w[i + 1], w[i + 2] = w[i + 1], w[i], w[i + 1]
            nb += 1
    return w, nb


def heap_canon(word):
    n = len(word); less = heap_less(word)
    used = [False] * n; out = []
    for _ in range(n):
        cands = [j for j in range(n) if not used[j] and all(used[i] for i in less[j])]
        j = min(cands, key=lambda j: (word[j], j))
        used[j] = True; out.append(word[j])
    return out


def packet_ok(vals):
    return sum(vals[i] != vals[i + 1] for i in range(len(vals) - 1)) <= 1


def is_sig(s, m):
    for P in C(range(m), 4):
        a, b, c, d = P
        if not packet_ok([s[(a, b, c)], s[(a, b, d)], s[(a, c, d)], s[(b, c, d)]]):
            return False
    return True


def find_order(s, v, m):
    """A flip order of D(s, v) through signotopes (DFS); exists for the cases used here."""
    D = [t for t in s if s[t] != v[t]]
    cur = dict(s)

    def dfs(left, acc):
        if not left:
            return list(acc)
        for t in list(left):
            cur[t] = not cur[t]
            if is_sig(cur, m):
                left.remove(t); acc.append(t)
                r = dfs(left, acc)
                if r is not None:
                    return r
                left.add(t); acc.pop()
            cur[t] = not cur[t]
        return None
    return dfs(set(D), [])


def cert(L, Lp, m, order):
    moves = []
    w = list(L)
    for T in order:
        w2 = braid_flip(w, m, T, moves)
        assert w2 is not None, ("blocked", T)
        w = w2
    # final commutations to reach Lp exactly
    assert heap_canon(w) == heap_canon(Lp), "not commutation equivalent at the end"
    # bubble w into Lp: match letters of Lp to w by heap structure (greedy: same letter, leftmost available
    # with all heap predecessors used)
    less = heap_less(w)
    used = [False] * len(w); target = []
    for x in Lp:
        for j in range(len(w)):
            if not used[j] and w[j] == x and all(used[i] for i in less[j]):
                used[j] = True; target.append(j); break
        else:
            raise AssertionError("cannot match")
    w = bubble(w, target, moves)
    assert w == list(Lp)
    return moves


def case_words(case):
    kind = case[0]
    if kind == 'pp':
        return [0], [0], 2
    if kind == 'Xp':
        a = case[1]; return bead(a, 0) + [2, 1, 0], [2, 1, 0] + bead(a, 1), 4
    if kind == 'pX':
        a = case[1]; return bead(a, 1) + [0, 1, 2], [0, 1, 2] + bead(a, 0), 4
    if kind == 'XX':
        a, b = case[1], case[2]
        return bead(a, 0) + bead(b, 3) + move_word(3, 3), move_word(3, 3) + bead(b, 0) + bead(a, 3), 6
    if kind == 'cell':
        a, b = case[1], case[2]
        return bead(a, 0) + bead(b, 4) + KAPPA, KAPPA + bead(b, 0) + bead(a, 4), 7


TABLE2 = {(1, 0): "127,124,126,125,137,146,136,145,135,134,247,267,257,256,467,457,456,367,357,347,356,346,245,235,234,236,237,167,157,156",
          (0, 1): "237,137,127,156,256,456,356,346,245,145,235,135,125,234,134,124,236,136,126,146,457,357,257,157,347,367,247,267,467,167",
          (1, 1): "127,124,126,125,137,146,136,145,135,134,247,256,257,267,456,457,467,356,357,367,347,346,245,235,234,236,237,156,157,167"}


def table2(eps):
    return [tuple(int(ch) - 1 for ch in t) for t in TABLE2[eps].split(",")]


def all_certs():
    out = {}
    cases = [('pp',)] + [('Xp', a) for a in (0, 1)] + [('pX', a) for a in (0, 1)] + \
            [('XX', a, b) for a in (0, 1) for b in (0, 1)] + [('cell', a, b) for a, b in [(1, 0), (0, 1), (1, 1)]]
    for case in cases:
        L, Lp, m = case_words(case)
        s, v = sig(L, m), sig(Lp, m)
        if case[0] == 'cell':
            order = table2((case[1], case[2]))
        else:
            order = find_order(s, v, m)
        assert sorted(order) == sorted(t for t in s if s[t] != v[t])
        moves = cert(L, Lp, m, order)
        w, nb = replay(L, moves)
        assert w == Lp and nb == len(order)
        out[case] = (L, Lp, m, moves, nb)
    return out




def lean_name(case):
    if case[0] == 'pp':
        return 'cert_pp'
    return 'cert_' + case[0] + ''.join(str(x) for x in case[1:])


def lean_moves(moves):
    return "[" + ", ".join((".c " if k == 'c' else ".b ") + str(i) for k, i in moves) + "]"


def emit_lean():
    lines = []
    for case, (L, Lp, m, moves, nb) in all_certs().items():
        lines.append(f"/-- {case}: {len(moves)} moves, {nb} braid moves. -/")
        body = lean_moves(moves)
        # wrap long lines
        toks = body[1:-1].split(", ")
        chunks, cur = [], ""
        for t in toks:
            if len(cur) + len(t) + 2 > 100:
                chunks.append(cur); cur = ""
            cur += (", " if cur else "") + t
        if cur:
            chunks.append(cur)
        lines.append(f"def {lean_name(case)} : List Mv := [")
        for j, ch in enumerate(chunks):
            lines.append("  " + ch + ("," if j < len(chunks) - 1 else "]"))
        if not chunks:
            lines[-1] = f"def {lean_name(case)} : List Mv := []"
        lines.append("")
    return "\n".join(lines)


HEADER = '''import BraidDistance.Cases

/-!
# Explicit sequences of commutations and braid moves for the local cases (Lemma 4.5(b), Table 2)

A certificate is a list of moves on a word:
* `Mv.c i`: a commutation of the letters at the indices `i, i+1` (they must differ by at least `2`);
* `Mv.b i`: a braid move on the letters at the indices `i, i+1, i+2` (`x, x±1, x ↦ x±1, x, x±1`).

`runMvs w ms` replays the moves (failing with `none` if a move does not apply) and returns the final word and the
number of braid moves; `checkCert w w' k ms` checks that `ms` leads from `w` to `w'` with `k` braid moves.
Soundness (`checkCert_sound` in `PathLemmas.lean`) turns a successful check into a `Path w w' k`.

The certificates below were generated by `scripts/gen_certs.py`.  For the cells they follow the orders of
Table 2 of the paper; for the other cases an order found by search through signotopes.  For each triple in the
order, the word is reordered by commutations so that the three letters of the triple are consecutive, and the
braid move is applied; a final reordering by commutations reaches `L'` exactly.  The certificate for
`cell false false` (32 braid moves) is not listed: it is obtained from `cell true false` by turning the bead of
the block `U` over before and back after (Proposition 3.2(b)).
-/

namespace BraidDistance

/-- A move of a certificate. -/
inductive Mv where
  /-- Commutation of the letters at the indices `i, i+1`. -/
  | c (i : Nat)
  /-- Braid move on the letters at the indices `i, i+1, i+2`. -/
  | b (i : Nat)
deriving DecidableEq, Repr

/-- Apply one move, or fail. -/
def applyMv (w : List Nat) : Mv → Option (List Nat)
  | .c i => match w.drop i with
    | x :: y :: rest => if x + 2 ≤ y ∨ y + 2 ≤ x then some (w.take i ++ y :: x :: rest) else none
    | _ => none
  | .b i => match w.drop i with
    | x :: y :: z :: rest =>
      if x = z ∧ (y = x + 1 ∨ x = y + 1) then some (w.take i ++ y :: x :: y :: rest) else none
    | _ => none

/-- The number of braid moves of a move. -/
def Mv.cost : Mv → Nat
  | .c _ => 0
  | .b _ => 1

/-- Replay a list of moves; returns the final word and the number of braid moves. -/
def runMvs : List Nat → List Mv → Option (List Nat × Nat)
  | w, [] => some (w, 0)
  | w, mv :: ms => match applyMv w mv with
    | none => none
    | some w' => match runMvs w' ms with
      | none => none
      | some (w'', k) => some (w'', mv.cost + k)

/-- `ms` leads from `w` to `w'` with exactly `k` braid moves. -/
def checkCert (w w' : List Nat) (k : Nat) (ms : List Mv) : Bool := runMvs w ms == some (w', k)

'''

FOOTER = '''
/-- The certificate of a case (`none` for `cell false false`). -/
def Case.cert : Case → Option (List Mv)
  | .pp => some cert_pp
  | .Xp false => some cert_Xp0
  | .Xp true => some cert_Xp1
  | .pX false => some cert_pX0
  | .pX true => some cert_pX1
  | .XX false false => some cert_XX00
  | .XX false true => some cert_XX01
  | .XX true false => some cert_XX10
  | .XX true true => some cert_XX11
  | .cell true false => some cert_cell10
  | .cell false true => some cert_cell01
  | .cell true true => some cert_cell11
  | .cell false false => none

end BraidDistance
'''

def write_lean(path):
    """Write BraidDistance/Certificates.lean."""
    with open(path, "w") as f:
        f.write(HEADER + emit_lean() + FOOTER)


if __name__ == "__main__":
    import os, sys
    for case, (L, Lp, m, moves, nb) in all_certs().items():
        print(case, "len", len(L), "moves", len(moves), "braid", nb)
    if len(sys.argv) > 1 and sys.argv[1] == "--write":
        here = os.path.dirname(os.path.abspath(__file__))
        write_lean(os.path.join(here, "..", "BraidDistance", "Certificates.lean"))
        print("wrote Certificates.lean")
