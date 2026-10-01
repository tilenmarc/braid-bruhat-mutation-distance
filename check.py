"""Computer checks accompanying the paper `main.tex` (shortest mutation paths are NP-hard).

Everything is written from the definitions in the paper, with 1-based labels: wires/elements 1..m,
positions 1..m, the letter s_i swaps the wires at positions i and i+1; the extra element of the positive
fibre is INF, placed above all other elements.

  python check.py        run every check (about 4 minutes)

Checks (names refer to the labels in main.tex)
  [1]  packet cycle (lem:C8), |B(m,2)| for m <= 7, Table tab:local and lem:local(b)
  [2]  lem:sW on random reduced words: signotope, local sequences = crossing orders, part (d)
  [3]  lem:sigchi(b) and prop:fibre (INF on top), exhaustive for small (|S|, r)
  [4]  lem:packet against replay on random pairs
  [5]  lem:oneline, by running the chain argument of its proof, on all pairs agreeing off one element
  [6]  the gadget: strings, D, crossing order of wire 4 (K3), the cycle of tab:cycle, the four BFS distances of
       prop:gadget(b), the orders of tab:seq30, the 32-flip walk (proof of prop:lowerW), sec:gadget (why seven wires) (symmetry)
  Sections [1], [2], [5] and parts of [6] also check material of earlier versions of the paper (local sequences,
  the one-wire lemma, sweeps, height certificates); they are kept as additional regression checks.
  [7]  the construction: lem:step, cor:edgeD and the walk of prop:upper on 27 graphs
  [8]  obs:normal on all rank-3 chirotopes on five elements
  [9]  lem:lift, lem:liftflip, the minor identity in prop:excess, and the arithmetic of thm:allranks
  [10] the maximal excess over all pairs of B(6,2) is 2
  [11] sec:gadget (why seven wires): the 60 cells, and kappa is the only OR cell
"""
import itertools
import random
from collections import deque
from math import comb

C = itertools.combinations
INF = 10 ** 6


# ---------------------------------------------------------------- signotopes
def packet_ok(vals):
    return sum(vals[i] != vals[i + 1] for i in range(len(vals) - 1)) <= 1


def rsets_lex(P):
    """The (|P|-1)-subsets of the sorted tuple P in lexicographic order (omit the largest first)."""
    return [tuple(x for x in P if x != y) for y in reversed(P)]


def is_signotope(u, S, r):
    return all(packet_ok([u[X] for X in rsets_lex(P)]) for P in C(sorted(S), r + 1))


def packets_ok_at(u, T, S, r):
    """Signotope condition on the packets containing the r-set T only."""
    for y in S:
        if y not in T:
            P = tuple(sorted(T + (y,)))
            if not packet_ok([u[X] for X in rsets_lex(P)]):
                return False
    return True


def all_signotopes(m, r):
    sigs = [dict()]
    for k in range(r, m + 1):
        newsets = [X for X in C(range(1, k + 1), r) if X[-1] == k]
        packs = [P for P in C(range(1, k + 1), r + 1) if P[-1] == k]
        new = []
        for s in sigs:
            for bits in itertools.product((1, -1), repeat=len(newsets)):
                s2 = dict(s)
                s2.update(zip(newsets, bits))
                if all(packet_ok([s2[X] for X in rsets_lex(P)]) for P in packs):
                    new.append(s2)
        sigs = new
    return sigs


def fmt(s, m):
    return "".join("+" if s[x] > 0 else "-" for x in C(range(1, m + 1), 3))


# ---------------------------------------------------------------- reduced words
def sig_of_word(word, m):
    pos = list(range(1, m + 1))
    t = {}
    for k, i in enumerate(word):
        a, b = pos[i - 1], pos[i]
        key = (min(a, b), max(a, b))
        assert key not in t, "pair swapped twice"
        t[key] = k
        pos[i - 1], pos[i] = b, a
    assert len(t) == m * (m - 1) // 2, "not a reduced word"
    return {(a, b, c): (1 if t[(a, b)] < t[(b, c)] else -1) for a, b, c in C(range(1, m + 1), 3)}, t


# ---------------------------------------------------------------- chirotopes
def perm_sign(tup):
    s = 1
    for i in range(len(tup)):
        for j in range(i + 1, len(tup)):
            if tup[i] > tup[j]:
                s = -s
    return s


def chi_val(chi, tup):
    return perm_sign(tup) * chi[tuple(sorted(tup))]


def is_chirotope(chi, E, r):
    E = sorted(E)
    for sigma in C(E, r - 2):
        rest = [x for x in E if x not in sigma]
        for a, b, c, d in C(rest, 4):
            v = lambda x, y: chi_val(chi, sigma + (x, y))
            T = (v(a, b) * v(c, d), -v(a, c) * v(b, d), v(a, d) * v(b, c))
            if T[0] == T[1] == T[2]:
                return False
    return True


def F(u, S, r):
    """Positive fibre with INF on top: + on bases through INF."""
    chi = {}
    for B in C(sorted(S) + [INF], r):
        chi[B] = 1 if INF in B else u[B]
    return chi


# ---------------------------------------------------------------- packets and local sequences
CYC = ["++++", "+++-", "++--", "+---", "----", "---+", "--++", "-+++"]


def pstr(s, P):
    a, b, c, d = P
    return "".join("+" if s[X] > 0 else "-" for X in [(a, b, c), (a, b, d), (a, c, d), (b, c, d)])


def arc_orders(x, y, P):
    names = [(P[0], P[1], P[2]), (P[0], P[1], P[3]), (P[0], P[2], P[3]), (P[1], P[2], P[3])]
    i, j = CYC.index(x), CYC.index(y)
    k = sum(x[r] != y[r] for r in range(4))
    out = []
    if (j - i) % 8 == k:
        out.append([names[3 - ((i + r) % 4)] for r in range(k)])
    if (i - j) % 8 == k and k > 0:
        out.append([names[3 - ((i - r - 1) % 4)] for r in range(k)])
    if k == 4 and len(out) == 2 and out[0] == out[1]:
        out = out[:1]
    return out, k


def order_valid_by_packets(s, v, order, m):
    pos = {t: n for n, t in enumerate(order)}
    for P in C(range(1, m + 1), 4):
        arcs, k = arc_orders(pstr(s, P), pstr(v, P), P)
        if k < 2:
            continue
        if sorted([t for t in pos if set(t) <= set(P)], key=lambda t: pos[t]) not in arcs:
            return False
    return True


def order_valid_by_replay(s, order, S):
    cur = dict(s)
    for t in order:
        cur[t] = -cur[t]
        if not packets_ok_at(cur, t, S, 3):
            return False
    return True


def local_seq(s, l, S):
    """The order <_l on S minus l, as a list."""
    others = [x for x in S if x != l]
    import functools
    def cmp(b, c):
        if b == c:
            return 0
        lo, hi = min(b, c), max(b, c)
        v = s[tuple(sorted((l, lo, hi)))]
        # lo <_l hi iff s(l,lo,hi) = +
        before = (v > 0)
        return -1 if (b == lo) == before else 1
    return sorted(others, key=functools.cmp_to_key(cmp))


def oneline_walk(s, v, x, S):
    """The walk of lem:oneline, found by the chain argument of its proof. Returns the flip order."""
    cur = dict(s)
    order = []
    while True:
        D = [T for T in cur if cur[T] != v[T]]
        if not D:
            return order
        assert all(x in T for T in D)
        seq = {a: local_seq(cur, a, S) for a in S if a != x}
        N = {a: {b for b in S if b not in (a, x) and tuple(sorted((a, b, x))) in D} for a in seq}
        def e(a):
            L = seq[a]
            ix = L.index(x)
            for d in (1, -1):              # the element of N_a adjacent to x
                j = ix + d
                if 0 <= j < len(L) and L[j] in N[a]:
                    return L[j]
            raise AssertionError("N_a not an interval next to x")
        a = next(a for a in seq if N[a])
        seen = 0
        while True:
            b = e(a)
            if e(b) == a:
                T = tuple(sorted((a, b, x)))
                break
            a = b
            seen += 1
            assert seen <= len(S) + 2, "chain did not close"
        cur[T] = -cur[T]
        assert packets_ok_at(cur, T, S, 3), "the chain argument produced an invalid flip"
        order.append(T)


def bfs_dist(s, v, sigs, m):
    key = lambda x: fmt(x, m)
    idx = {key(x) for x in sigs}
    start, goal = key(s), key(v)
    dist = {start: 0}
    q = deque([start])
    while q:
        a = q.popleft()
        if a == goal:
            return dist[a]
        for n in range(len(a)):
            b = a[:n] + ("-" if a[n] == "+" else "+") + a[n + 1:]
            if b in idx and b not in dist:
                dist[b] = dist[a] + 1
                q.append(b)


# ---------------------------------------------------------------- the gadget
KAPPA = [4, 3, 2, 1, 4, 3, 5, 4, 3, 2, 6, 5, 4, 3, 4]


def bead(q, flipped):
    return [q + 1, q, q + 1] if flipped else [q, q + 1, q]


def gadget(e1, e2):
    return (sig_of_word(bead(1, e1) + bead(5, e2) + KAPPA, 7)[0],
            sig_of_word(KAPPA + bead(1, e2) + bead(5, e1), 7)[0])


def sweep(t, j, sign, use_max=False):
    t2 = dict(t)
    for T in t2:
        if (max(T) if use_max else min(T)) == j:
            t2[T] = sign
    return t2


SWEEP_TABLE = [  # (chain, operation list applied in order, expected changed sets per step, without the bead triple)
    ("s", [(1, -1, False), (2, 1, False)],
     [{124, 125, 126, 127, 134, 135, 136, 137, 145, 146}, {247, 256, 257, 267}]),
    ("v", [(1, -1, False), (2, 1, False), (3, -1, False), (4, -1, False)],
     [{156, 157, 167}, {234, 235, 236, 237, 245}, {346, 347, 356, 357, 367}, {456, 457, 467}]),
    ("s", [(7, -1, True), (6, 1, True), (5, -1, True), (4, -1, True)],
     [{127, 137, 237}, {156, 256, 346, 356, 456}, {125, 135, 145, 235, 245}, {124, 134, 234}]),
    ("v", [(7, -1, True), (6, 1, True)],
     [{157, 167, 247, 257, 267, 347, 357, 367, 457, 467}, {126, 136, 146, 236}]),
]
HEIGHTS = {(1, 0): ([0, -1, -9, 1, 9, 4, 0], [0, 6, 5, 1, -4, -3, 0]),
           (0, 1): ([0, -3, -4, 1, 5, 6, 0], [0, 4, 9, 1, -9, -1, 0]),
           (1, 1): ([0, -1, -3, 1, 4, 4, 0], [0, 4, 4, 1, -3, -1, 0])}


def num(T):
    return int("".join(map(str, T)))


def route_walk(eps):
    """The two routes of lem:gadgettight; returns the lengths, and checks every flip."""
    S = list(range(1, 8))
    gs, gv = gadget(*eps)
    lengths = []
    for part in (0, 2):                        # route 1: rows 0,1 ; route 2: rows 2,3
        (c1, ops1, exp1), (c2, ops2, exp2) = SWEEP_TABLE[part], SWEEP_TABLE[part + 1]
        chains = {}
        for chain, ops, exp in [(c1, ops1, exp1), (c2, ops2, exp2)]:
            t = dict(gs if chain == "s" else gv)
            states = [t]
            for (j, sign, use_max), expected in zip(ops, exp):
                t2 = sweep(t, j, sign, use_max)
                assert is_signotope(t2, S, 3)
                changed = {num(T) for T in t2 if t2[T] != t[T]}
                bead_t = 567 if use_max else 123
                assert changed - {bead_t} == expected, (eps, chain, j, changed, expected)
                states.append(t2)
                t = t2
            chains[chain] = states
        assert chains["s"][-1] == chains["v"][-1], "the two chains do not meet"
        # walk: forward along the s-chain, backward along the v-chain; each step by lem:oneline
        path = chains["s"] + list(reversed(chains["v"]))[1:]
        L = 0
        for a, b in zip(path, path[1:]):
            diff = [T for T in a if a[T] != b[T]]
            common = set(diff[0])
            for T in diff:
                common &= set(T)
            x = sorted(common)[0]
            o = oneline_walk(a, b, x, S)
            assert len(o) == len(diff)
            L += len(o)
        lengths.append(L)
    return lengths


# ---------------------------------------------------------------- the construction
def construct(n, edges):
    E = sorted((min(a, b), max(a, b)) for a, b in edges)
    Eset = set(E)
    up = {u: sorted(w for (x, w) in E if x == u) for u in range(1, n + 1)}
    groups = []
    for u in range(1, n + 1):
        groups.append(("X", u))
        groups += [("p", (u, w)) for w in up[u]]
    grp = {g: (g[1] if g[0] == "X" else g[1][0]) for g in groups}
    size = {g: (3 if g[0] == "X" else 1) for g in groups}
    lines, nxt = {}, 1
    for g in groups:
        lines[g] = list(range(nxt, nxt + size[g]))
        nxt += size[g]
    m = nxt - 1
    rank = {g: k for k, g in enumerate(groups)}
    order, swapped, events = list(groups), set(), []

    def swap_at(i):
        g, h = order[i], order[i + 1]
        assert frozenset((g, h)) not in swapped and rank[g] < rank[h]
        swapped.add(frozenset((g, h)))
        order[i], order[i + 1] = h, g
        events.append(("swap", g, h))

    bundle = {u: [("X", u)] + [("p", (u, w)) for w in up[u]] for u in range(1, n + 1)}
    for u in range(1, n + 1):                  # round u: B_u crosses B_{u+1}, ..., B_n
        for w in range(u + 1, n + 1):
            for z in bundle[w]:                # groups of B_w from the top
                if z == ("X", w) and (u, w) in Eset:
                    p = ("p", (u, w))
                    while order[order.index(z) - 1] != p:
                        assert grp[order[order.index(z) - 1]] == u
                        swap_at(order.index(z) - 1)
                    i = order.index(z) - 2
                    assert order[i] == ("X", u) and order[i + 1] == p
                    for key in [(p, z), (("X", u), z), (("X", u), p)]:
                        assert frozenset(key) not in swapped
                        swapped.add(frozenset(key))
                    order[i], order[i + 2] = z, ("X", u)
                    events.append(("cell", ("X", u), p, z))
                while order.index(z) > 0 and grp[order[order.index(z) - 1]] == u:
                    swap_at(order.index(z) - 1)
    for u in range(1, n + 1):                  # completion: for j = 2..k, p_{uw_j} passes up through Pi_u above it
        P = [g for g in groups if g[0] == "p" and grp[g] == u]
        for g in P[1:]:
            while order.index(g) > 0 and order[order.index(g) - 1] in P:
                swap_at(order.index(g) - 1)
    assert len(swapped) == len(groups) * (len(groups) - 1) // 2 and order == list(reversed(groups))
    wires = [x for g in groups for x in lines[g]]
    factors = []
    for ev in events:
        if ev[0] == "swap":
            _, g, h = ev
            a = min(wires.index(x) for x in lines[g]) + 1
            letters = []
            for j in range(size[h]):
                top = a + size[g] + j
                letters += list(range(top - 1, a + j - 1, -1))
            kind = {(3, 3): "XX", (3, 1): "Xp", (1, 3): "pX", (1, 1): "pp"}[(size[g], size[h])]
        else:
            _, g, p, h = ev
            a = min(wires.index(x) for x in lines[g]) + 1
            letters = [a - 1 + i for i in KAPPA]
            kind = "cell"
        before = {u: min(wires.index(x) for x in lines[("X", u)]) + 1 for u in range(1, n + 1)}
        for i in letters:
            wires[i - 1], wires[i] = wires[i], wires[i - 1]
        after = {u: min(wires.index(x) for x in lines[("X", u)]) + 1 for u in range(1, n + 1)}
        factors.append(dict(kind=kind, ev=ev, letters=letters, before=before, after=after))
    return dict(n=n, E=E, groups=groups, lines=lines, m=m, factors=factors, grp=grp)


def word_with_beads(con, k, eps):
    fs = con["factors"]
    w = [x for f in fs[:k] for x in f["letters"]]
    pos = fs[k]["before"] if k < len(fs) else fs[-1]["after"]
    for u, q in sorted(pos.items(), key=lambda kv: kv[1]):
        w += bead(q, eps.get(u, 0))
    return w + [x for f in fs[k:] for x in f["letters"]]


def sG_vG(con):
    K = len(con["factors"])
    return sig_of_word(word_with_beads(con, 0, {}), con["m"])[0], sig_of_word(word_with_beads(con, K, {}), con["m"])[0]


def gadget_cell_walk(eps):
    """A Hamming-tight flip order for the gadget pair eps != (0,0), from the routes of lem:gadgettight."""
    S = list(range(1, 8))
    gs, gv = gadget(*eps)
    part = 0 if eps[0] == 1 else 2
    (c1, ops1, _), (c2, ops2, _) = SWEEP_TABLE[part], SWEEP_TABLE[part + 1]
    ch = {}
    for chain, ops in [(c1, ops1), (c2, ops2)]:
        t = dict(gs if chain == "s" else gv)
        st = [t]
        for j, sign, use_max in ops:
            t = sweep(t, j, sign, use_max)
            st.append(t)
        ch[chain] = st
    path = ch["s"] + list(reversed(ch["v"]))[1:]
    order = []
    for a, b in zip(path, path[1:]):
        diff = [T for T in a if a[T] != b[T]]
        common = set(diff[0])
        for T in diff:
            common &= set(T)
        order += oneline_walk(a, b, sorted(common)[0], S)
    assert len(order) == 30
    return order


def tight_order(cur, triples, S):
    for perm in itertools.permutations(triples):
        ok = True
        for i, T in enumerate(perm):
            cur[T] = -cur[T]
            if not packets_ok_at(cur, T, S, 3):
                ok = False
                for U in perm[:i + 1]:
                    cur[U] = -cur[U]
                break
        if ok:
            return list(perm)
    raise AssertionError("no arc order")


def walk(con, cover, check_words=False):
    m, L = con["m"], con["lines"]
    S = list(range(1, m + 1))
    sG, vG = sG_vG(con)
    cur, length = dict(sG), 0
    eps = {u: 1 for u in cover}
    cell_orders = {e: gadget_cell_walk(e) for e in [(1, 0), (0, 1), (1, 1)]}

    def flip(T):
        nonlocal length
        cur[T] = -cur[T]
        assert packets_ok_at(cur, T, S, 3), "invalid flip"
        length += 1

    for u in cover:
        flip(tuple(L[("X", u)]))
    for k, f in enumerate(con["factors"]):
        if check_words:
            assert cur == sig_of_word(word_with_beads(con, k, eps), m)[0]
            nxt = sig_of_word(word_with_beads(con, k + 1, eps), m)[0]
            Dk = {T for T in cur if cur[T] != nxt[T]}
        kind, ev = f["kind"], f["ev"]
        before = length
        if kind in ("Xp", "pX"):
            X = L[ev[1]] if kind == "Xp" else L[ev[2]]
            z = L[ev[2]][0] if kind == "Xp" else L[ev[1]][0]
            length += len(tight_order(cur, [tuple(sorted((a, b, z))) for a, b in C(X, 2)], S))
        elif kind == "XX":                         # prop:upper, case (XX): X above Y
            X, Y = L[ev[1]], L[ev[2]]
            for y in sorted(Y, reverse=True):
                length += len(tight_order(cur, [tuple(sorted((a, b, y))) for a, b in C(X, 2)], S))
            for x in sorted(X, reverse=True):
                length += len(tight_order(cur, [tuple(sorted((x, a, b))) for a, b in C(Y, 2)], S))
        elif kind == "cell":
            _, Xu, p, Xw = ev
            A = L[Xu] + L[p] + L[Xw]
            key = (eps.get(Xu[1], 0), eps.get(Xw[1], 0))
            assert key != (0, 0), "not a vertex cover"
            for T in cell_orders[key]:
                flip(tuple(A[i - 1] for i in T))
        if check_words:                             # lem:step: D_k as stated, flipped exactly once
            assert len(Dk) == length - before
            assert len(Dk) == {"pp": 0, "Xp": 3, "pX": 3, "XX": 18, "cell": 30}[kind]
            assert cur == nxt
    for u in cover:
        flip(tuple(L[("X", u)]))
    assert cur == vG
    return length


def min_vc(n, edges):
    for k in range(n + 1):
        for S in C(range(1, n + 1), k):
            if all(a in S or b in S for a, b in edges):
                return k, S


# ---------------------------------------------------------------- higher ranks
def lift(s, S, Nset, r):
    """L^r_N s on N u S (N below S): s(top_3 X) if |X & S| >= 3, else +."""
    ground = sorted(Nset) + sorted(S)
    Sset = set(S)
    return {X: (s[X[-3:]] if len(Sset & set(X)) >= 3 else 1) for X in C(ground, r)}


def drop_min_walk(v, vX, X, G, ell, k):
    """Flip order of the sets Q_x = {x} u X (inner claim of lem:liftflip), by the insertion rule."""
    tau = v[X]
    Lam = [x for x in G if x < X[0]]
    order = [ell]
    for x in Lam:                              # increasing; early to the front, late to the back
        alpha = {v[tuple(sorted(set((x,) + X) - {t}))] for t in X}
        assert len(alpha) == 1
        if alpha.pop() == tau:
            order.insert(0, x)
        else:
            order.append(x)
    return [tuple(sorted((x,) + X)) for x in order]


def liftflip_walk(s, S, Nset, r, T):
    """The walk of lem:liftflip from L^r_N s to L^r_N s^T, built by the induction of the proof."""
    q = r - 3
    if q == 0:
        return [T]
    Nl = sorted(Nset)
    ell, N1 = Nl[0], Nl[1:]
    prev = liftflip_walk(s, S, N1, r - 1, T)
    # replay the lower walk and lift each flip by drop_min_walk
    G = N1 + sorted(S)
    cur_low = lift(s, S, N1, r - 1)
    out = []
    for Xs in prev:
        nxt_low = dict(cur_low)
        nxt_low[Xs] = -nxt_low[Xs]
        out += drop_min_walk(cur_low, nxt_low, Xs, G, ell, r - 1)
        cur_low = nxt_low
    return out


def find_cell(groups, target):
    """A word on 7 positions swapping each cross-group pair once and no pair inside a group, in which the
    p-wire meets the block wires in the order `target` (DFS); None if there is none."""
    p = groups["p"][0]
    grp = {w: g for g, ws in groups.items() for w in ws}
    need = {frozenset((a, b)) for a, b in C(range(1, 8), 2) if grp[a] != grp[b]}
    failed = set()

    def rec(arr, done, k, word):
        if len(done) == len(need):
            return word
        if (arr, done) in failed:
            return None
        for i in range(6):
            a, b = arr[i], arr[i + 1]
            pr = frozenset((a, b))
            if pr in done or pr not in need:
                continue
            k2 = k
            if p in pr:
                if target[k] != (a if b == p else b):
                    continue
                k2 = k + 1
            arr2 = list(arr)
            arr2[i], arr2[i + 1] = b, a
            res = rec(tuple(arr2), done | {pr}, k2, word + [i + 1])
            if res is not None:
                return res
        failed.add((arr, done))
        return None
    return rec(tuple(range(1, 8)), frozenset(), 0, [])


def check_unique(sigs7):
    """sec:gadget (why seven wires): among the 60 cells, only kappa has excess (2,0,0,0) over eps = 00,10,01,11."""
    keys = {fmt(s, 7) for s in sigs7}
    tr = list(C(range(1, 8), 3))

    def dist(s, v):
        a, goal = fmt(s, 7), fmt(v, 7)
        seen = {a: 0}
        q = deque([a])
        while q:
            x = q.popleft()
            if x == goal:
                return seen[x]
            for n in range(35):
                y = x[:n] + ("-" if x[n] == "+" else "+") + x[n + 1:]
                if y in keys and y not in seen:
                    seen[y] = seen[x] + 1
                    q.append(y)
    placements = {"between": dict(U=[1, 2, 3], p=[4], V=[5, 6, 7]),
                  "above": dict(p=[1], U=[2, 3, 4], V=[5, 6, 7]),
                  "below": dict(U=[1, 2, 3], V=[4, 5, 6], p=[7])}
    found, ors = [], 0
    for name, g in placements.items():
        U, V, p = g["U"], g["V"], g["p"][0]
        uo = U[::-1] if p > max(U) else U
        vo = V[::-1] if p > max(V) else V
        for posU in C(range(6), 3):
            order, iu, iv = [], 0, 0
            for k in range(6):
                if k in posU:
                    order.append(uo[iu]); iu += 1
                else:
                    order.append(vo[iv]); iv += 1
            w = find_cell(g, order)
            assert w is not None
            arr = list(range(1, 8))
            for i in w:
                arr[i - 1], arr[i] = arr[i], arr[i - 1]
            qU1, qV1 = min(arr.index(x) for x in U) + 1, min(arr.index(x) for x in V) + 1
            pattern = []
            for e in [(0, 0), (1, 0), (0, 1), (1, 1)]:
                s = sig_of_word(bead(U[0], e[0]) + bead(V[0], e[1]) + w, 7)[0]
                v = sig_of_word(w + bead(qU1, e[0]) + bead(qV1, e[1]), 7)[0]
                pattern.append(dist(s, v) - sum(1 for T in tr if s[T] != v[T]))
            if pattern == [2, 0, 0, 0]:
                found.append((name, tuple(order)))
                ors += 1
    return found


def main():
    rng = random.Random(20260925)
    print("[1] packets, small Bruhat orders, local sequences")
    mono = ["".join(v) for v in itertools.product("+-", repeat=4) if packet_ok(list(v))]
    assert sorted(mono) == sorted(CYC)
    for a in range(8):
        assert [r for r in range(4) if CYC[a][r] != CYC[(a + 1) % 8][r]] == [3 - (a % 4)]
    sig3 = {m: all_signotopes(m, 3) for m in range(3, 8)}
    assert [len(sig3[m]) for m in range(3, 8)] == [2, 8, 62, 908, 24698]
    table = {"++++": ("234 134 124 123", "3,3,2,2", {123, 234}),
             "+++-": ("234 143 142 132", "3,4,4,3", {134, 234}),
             "++--": ("243 143 412 312", "4,4,1,1", {124, 134}),
             "+---": ("423 413 412 321", "2,1,1,2", {123, 124})}
    for s in sig3[4]:
        st = pstr(s, (1, 2, 3, 4))
        seqs = [local_seq(s, l, [1, 2, 3, 4]) for l in range(1, 5)]
        mids = [sq[1] for sq in seqs]
        assert all(mids.count(d) in (0, 2) for d in range(1, 5))           # lem:local(b)
        flip = {num(T) for T in s if is_signotope({**s, T: -s[T]}, range(1, 5), 3)}
        assert flip == {num(tuple(y2 for y2 in range(1, 5) if y2 != y)) for y in range(1, 5) if y not in mids}
        if st in table:
            assert " ".join("".join(map(str, q)) for q in seqs) == table[st][0]
            assert ",".join(map(str, mids)) == table[st][1] and flip == table[st][2]
    print("   |B(m,2)| =", [len(sig3[m]) for m in range(3, 8)], "; Table tab:local OK")

    print("[2] lem:sW on random reduced words")
    for m in range(4, 11):
        for _ in range(150):
            word, pos = [], list(range(1, m + 1))
            while True:
                cand = [i for i in range(1, m) if pos[i - 1] < pos[i]]
                if not cand:
                    break
                i = rng.choice(cand)
                word.append(i)
                pos[i - 1], pos[i] = pos[i], pos[i - 1]
            s, t = sig_of_word(word, m)
            assert is_signotope(s, range(1, m + 1), 3)
            for x in range(1, m + 1):                                      # (a): local sequence = crossing order
                assert local_seq(s, x, range(1, m + 1)) == sorted((y for y in range(1, m + 1) if y != x),
                                                                  key=lambda y: t[(min(x, y), max(x, y))])
            for x, x2, z in itertools.permutations(range(1, m + 1), 3):    # (d)
                if x < x2 and not (x < z < x2):
                    ts = sorted([t[(x, x2)], t[tuple(sorted((x, z)))], t[tuple(sorted((x2, z)))]])
                    first, last = t[(x, x2)] == ts[0], t[(x, x2)] == ts[2]
                    assert first or last
                    assert (s[tuple(sorted((x, x2, z)))] > 0) == ((first and z > x2) or (last and z < x))

    print("[3] lem:sigchi(b) and prop:fibre with INF on top")
    for (m, r) in [(4, 3), (5, 3), (5, 4), (6, 4), (6, 5), (7, 6), (4, 2), (5, 2)]:
        sets = list(C(range(1, m + 1), r))
        cnt = 0
        for bits in itertools.product((1, -1), repeat=len(sets)):
            u = dict(zip(sets, bits))
            a = is_signotope(u, range(1, m + 1), r)
            assert a == is_chirotope(F(u, range(1, m + 1), r), list(range(1, m + 1)) + [INF], r)
            assert not a or is_chirotope(u, list(range(1, m + 1)), r)             # lem:sigchi(b)
            cnt += a
        print(f"   (|S|,r)=({m},{r}): {2 ** len(sets)} maps, {cnt} signotopes, all agree; each signotope is a chirotope")
    for _ in range(400):
        u = rng.choice(sig3[6]) if rng.random() < 0.5 else {T: rng.choice((1, -1)) for T in C(range(1, 7), 3)}
        assert is_signotope(u, range(1, 7), 3) == is_chirotope(F(u, range(1, 7), 3), list(range(1, 7)) + [INF], 3)

    print("[4] lem:packet against replay")
    for _ in range(3000):
        s, v = rng.choice(sig3[6]), rng.choice(sig3[6])
        D = [T for T in s if s[T] != v[T]]
        rng.shuffle(D)
        assert order_valid_by_packets(s, v, D, 6) == order_valid_by_replay(s, D, list(range(1, 7)))

    print("[5] lem:oneline by the chain argument")
    for m in (4, 5, 6):
        S = list(range(1, m + 1))
        pairs = 0
        for x in S:
            groups = {}
            for s in sig3[m]:
                key = tuple(s[T] for T in sorted(s) if x not in T)
                groups.setdefault(key, []).append(s)
            for grp_ in groups.values():
                for s in grp_:
                    for v in grp_:
                        o = oneline_walk(s, v, x, S)
                        assert len(o) == sum(1 for T in s if s[T] != v[T])
                        pairs += 1
        print(f"   m={m}: {pairs} ordered pairs, all walks of length |D|")
    S7 = list(range(1, 8))
    for _ in range(3000):                                                  # m = 7: random pairs
        s = rng.choice(sig3[7])
        x = rng.randint(1, 7)
        key = tuple(s[T] for T in sorted(s) if x not in T)
        cands = [v for v in sig3[7][:4000] if tuple(v[T] for T in sorted(v) if x not in T) == key]
        if cands:
            v = rng.choice(cands)
            assert len(oneline_walk(s, v, x, S7)) == sum(1 for T in s if s[T] != v[T])

    print("[6] the gadget")
    gs, gv = gadget(0, 0)
    assert fmt(gs, 7) == "+++++++++++----++++++-------------+"
    assert fmt(gv, 7) == "+-----------+++-----+++++-+++++++++"
    D = {num(T) for T in gs if gs[T] != gv[T]}
    assert len(D) == 30 and {145, 146, 245, 247, 346, 347} <= D
    t_s = sig_of_word(bead(1, 0) + bead(5, 0) + KAPPA, 7)[1]
    t_v = sig_of_word(KAPPA + bead(1, 0) + bead(5, 0), 7)[1]
    order4 = lambda t: sorted([y for y in S7 if y != 4], key=lambda y: t[(min(4, y), max(4, y))])
    assert order4(t_s) == [7, 1, 2, 6, 5, 3] and order4(t_v) == [5, 3, 2, 6, 7, 1]
    for e in [(1, 0), (0, 1), (1, 1)]:
        s, v = gadget(*e)
        assert {num(T) for T in s if s[T] != v[T]} == D
        assert (s[(1, 2, 3)] == -1) == (e[0] == 1) and (s[(5, 6, 7)] == -1) == (e[1] == 1)
    cyc = [(1, 2, 4, 6), (1, 4, 6, 7), (4, 5, 6, 7), (2, 4, 5, 6), (2, 3, 4, 5), (1, 2, 3, 4)]
    succ = set()
    for P in cyc:
        arcs, k = arc_orders(pstr(gs, P), pstr(gv, P), P)
        assert k == 3 and len(arcs) == 1
        succ |= {(arcs[0][a], arcs[0][b]) for a in range(3) for b in range(a + 1, 3)}
    cycle = [124, 146, 467, 456, 245, 234]
    for a in range(6):
        pair = (cycle[a], cycle[(a + 1) % 6])
        assert any((num(x), num(y)) == pair for x, y in succ), pair
    for e in [(0, 0), (1, 0), (0, 1), (1, 1)]:
        l1, l2 = route_walk(e)
        assert l1 == 30 + 2 * (e[0] == 0) and l2 == 30 + 2 * (e[1] == 0)
    print("   sweeps and routes of lem:gadgettight: lengths 30+2[e1=0], 30+2[e2=0] for all e")
    for e in [(0, 0), (1, 0), (0, 1), (1, 1)]:                                # prop:gadget(b) by BFS
        assert bfs_dist(*gadget(*e), sig3[7], 7) == 30 + 2 * (e == (0, 0))
    print("   prop:gadget(b) by breadth-first search in B(7,2): distances 32, 30, 30, 30")
    for e, (y, z) in HEIGHTS.items():
        s, v = gadget(*e)
        for h, target in [(y, s), (z, v)]:
            for i, j, k in C(range(1, 8), 3):
                d = (j - i) * h[k - 1] - (k - i) * h[j - 1] + (k - j) * h[i - 1]
                assert d != 0 and (1 if d > 0 else -1) == target[(i, j, k)]
    bar = lambda s: {(a, b, c): s[(8 - c, 8 - b, 8 - a)] for a, b, c in C(S7, 3)}
    for e1, e2 in [(0, 0), (1, 0), (0, 1), (1, 1)]:
        assert bar(gadget(e1, e2)[0]) == gadget(e2, e1)[1]
    walk147 = ("147 167 157 156 247 267 257 256 467 367 457 357 347 456 245 145 356 235 135 125 346 234 134 124 "
               "236 136 126 146 237 137 127 147").split()
    cur = dict(gs)
    for w in walk147:                                                      # the 32-flip walk (proof of prop:lowerW)
        T = tuple(int(c) for c in w)
        cur[T] = -cur[T]
        assert packets_ok_at(cur, T, S7, 3) and is_chirotope(F(cur, S7, 3), S7 + [INF], 3)
    assert cur == gv and len(walk147) == 32 and walk147.count("147") == 2 and "123" not in walk147
    SEQ30 = {(1, 0): "127 124 126 125 137 146 136 145 135 134 247 267 257 256 467 "
                     "457 456 367 357 347 356 346 245 235 234 236 237 167 157 156",
             (0, 1): "237 137 127 156 256 456 356 346 245 145 235 135 125 234 134 "
                     "124 236 136 126 146 457 357 257 157 347 367 247 267 467 167",
             (1, 1): "127 124 126 125 137 146 136 145 135 134 247 256 257 267 456 "
                     "457 467 356 357 367 347 346 245 235 234 236 237 156 157 167"}
    for e, txt in SEQ30.items():                                           # Table tab:seq30
        s, v = gadget(*e)
        order = [tuple(int(c) for c in w) for w in txt.split()]
        assert len(order) == 30 and set(order) == {T for T in s if s[T] != v[T]}
        assert order_valid_by_packets(s, v, order, 7) and order_valid_by_replay(s, order, S7)
        cur = dict(s)
        for T in order:
            cur[T] = -cur[T]
        assert cur == v
    print("   strings, crossing orders, cycle, BFS 32, heights, symmetry, 32-flip walk (proof of prop:lowerW), tab:seq30: OK")

    print("[7] the construction")
    graphs = {"P2": (2, [(1, 2)]), "P3": (3, [(1, 2), (2, 3)]), "P4": (4, [(1, 2), (2, 3), (3, 4)]),
              "K3": (3, [(1, 2), (1, 3), (2, 3)]), "C4": (4, [(1, 2), (2, 3), (3, 4), (1, 4)]),
              "K13a": (4, [(1, 2), (1, 3), (1, 4)]), "K13b": (4, [(1, 4), (2, 4), (3, 4)]),
              "2K2": (4, [(1, 3), (2, 4)]), "K4": (4, list(C(range(1, 5), 2))), "K5": (5, list(C(range(1, 6), 2))),
              "P2+2K1": (4, [(2, 3)]), "empty3": (3, []),
              "Petersen": (10, [(1, 2), (2, 3), (3, 4), (4, 5), (5, 1), (1, 6), (2, 7), (3, 8), (4, 9), (5, 10),
                                (6, 8), (8, 10), (10, 7), (7, 9), (9, 6)]),
              "Q3": (8, [(1, 2), (2, 3), (3, 4), (4, 1), (5, 6), (6, 7), (7, 8), (8, 5), (1, 5), (2, 6), (3, 7), (4, 8)]),
              "K33": (6, [(a, b) for a in (1, 2, 3) for b in (4, 5, 6)])}
    for idx in range(12):
        nn = rng.randint(3, 8)
        graphs[f"random#{idx + 1}"] = (nn, [e for e in C(range(1, nn + 1), 2) if rng.random() < 0.4])
    g0s, g0v = gadget(0, 0)
    for name, (n, es) in graphs.items():
        con = construct(n, es)
        m = con["m"]
        sG, vG = sG_vG(con)
        assert is_signotope(sG, range(1, m + 1), 3) and is_signotope(vG, range(1, m + 1), 3)
        for (u, w) in con["E"]:                                              # cor:edgeD(a)
            A = con["lines"][("X", u)] + con["lines"][("p", (u, w))] + con["lines"][("X", w)]
            for T in C(range(1, 8), 3):
                TT = tuple(A[i - 1] for i in T)
                assert sG[TT] == g0s[T] and vG[TT] == g0v[T]
        Dn = sum(1 for T in sG if sG[T] != vG[T])
        assert Dn == 3 * n * (m - 3) + 6 * len(con["E"])                   # cor:edgeD(b)
        vc, cov = min_vc(n, con["E"])
        ln = walk(con, list(cov), check_words=(m <= 20))
        assert ln == Dn + 2 * vc
        extra = ""
        if n <= 5 and con["E"]:
            covers = [c for k in range(n + 1) for c in C(range(1, n + 1), k)
                      if all(a in c or b in c for a, b in con["E"])]
            for c in covers:
                assert walk(con, list(c)) == Dn + 2 * len(c)
            extra = f", all {len(covers)} covers"
        print(f"   {name}: m={m}, |D|={Dn}, VC={vc}, walk {ln}{extra}")

    print("[8] obs:normal on all rank-3 chirotopes on 5 elements")
    E5 = [1, 2, 3, 4, 5]
    bases = list(C(E5, 3))
    count = 0
    for bits in itertools.product((1, -1), repeat=len(bases)):
        chi = dict(zip(bases, bits))
        if not is_chirotope(chi, E5, 3):
            continue
        count += 1
        e, f = 5, 1
        eps = {j: 1 for j in E5}
        for j in E5:
            if j not in (e, f) and chi_val(chi, (e, f, j)) < 0:
                eps[j] = -1
        ch2 = {B: chi[B] * eps[B[0]] * eps[B[1]] * eps[B[2]] for B in bases}
        phi = lambda a, b: chi_val(ch2, (e, a, b))
        rest = [j for j in E5 if j != e]
        import functools
        rest.sort(key=functools.cmp_to_key(lambda a, b: 0 if a == b else (-1 if phi(a, b) > 0 else 1)))
        assert all(phi(rest[i], rest[j]) > 0 for i in range(4) for j in range(i + 1, 4))   # transitive
        pi = {rest[i]: i + 1 for i in range(4)}
        pi[e] = INF
        new = {}
        for B in bases:
            img = tuple(pi[b] for b in B)
            new[tuple(sorted(img))] = perm_sign(img) * ch2[B]
        assert all(new[B] == 1 for B in new if INF in B)
        s = {B: new[B] for B in new if INF not in B}
        assert is_signotope(s, [1, 2, 3, 4], 3)
    print(f"   {count} chirotopes normalized")

    print("[9] higher ranks")
    for m, sigs in [(4, sig3[4]), (5, sig3[5]), (6, sig3[6][:250])]:
        S = list(range(10, 10 + m))
        relabel = lambda s: {tuple(9 + x for x in T): val for T, val in s.items()}
        for nN, r in [(1, 4), (2, 4), (2, 5), (3, 5)]:
            if r - 3 > nN:
                continue
            Nset = list(range(10 - nN, 10))
            flips = 0
            for s0 in sigs:
                s = relabel(s0)
                u = lift(s, S, Nset, r)
                assert is_signotope(u, Nset + S, r)                                  # lem:lift(a)
                for T in C(S, 3):
                    sT = dict(s)
                    sT[T] = -sT[T]
                    if not packets_ok_at(sT, T, S, 3):
                        continue
                    uT = lift(sT, S, Nset, r)
                    diff = {X for X in u if u[X] != uT[X]}
                    a = sum(1 for x in S if x < T[0])
                    expect = {tuple(sorted(T + Y)) for Y in C([x for x in Nset + S if x < T[0]], r - 3)}
                    assert diff == expect and len(diff) == comb(nN + a, r - 3)       # lem:lift(c)
                    wk = liftflip_walk(s, S, Nset, r, T)
                    assert sorted(wk) == sorted(diff)
                    cur = dict(u)
                    for X in wk:
                        cur[X] = -cur[X]
                        assert packets_ok_at(cur, X, Nset + S, r)                    # lem:liftflip
                    assert cur == uT
                    flips += 1
            print(f"   |S|={m}, |N|={nN}, r={r}: {flips} lifted flips")
    # the minor identity (F_r L s)_Y = F_3 s
    for s0 in sig3[5][:30]:
        S = list(range(10, 15))
        s = {tuple(9 + x for x in T): val for T, val in s0.items()}
        Nset, r = [7, 8, 9], 5
        chi = F(lift(s, S, Nset, r), Nset + S, r)
        for Y in C(Nset, 2):
            minor = {Z: chi_val(chi, Y + Z) for Z in C(S + [INF], 3)}
            assert minor == F(s, S, 3)
    # arithmetic of thm:allranks
    for r in range(4, 9):
        q = r - 3
        for m in range(6, 40, 3):
            for k in range(1, m + 1, 4):
                n = q * m * (k + 1) + q
                A, W = comb(n, q), comb(n + m - 3, q)
                assert W * k < A * (k + 1)
                M = n + m
                assert comb(M, r) > 4 * W * comb(m, 3)
    print("[10] maximal excess in B(6,2) (isometry item of the open problems)")
    keys6 = [fmt(s, 6) for s in sig3[6]]
    idx6 = {k: i for i, k in enumerate(keys6)}
    maxex = 0
    D6 = {}
    for src_k in keys6:
        dist = {src_k: 0}
        q = deque([src_k])
        while q:
            a = q.popleft()
            for n in range(20):
                b = a[:n] + ("-" if a[n] == "+" else "+") + a[n + 1:]
                if b in idx6 and b not in dist:
                    dist[b] = dist[a] + 1
                    q.append(b)
        D6[src_k] = dist
        for b, d in dist.items():
            maxex = max(maxex, d - sum(1 for x, y in zip(src_k, b) if x != y))
    assert maxex == 2
    print("   maximal excess d_B - |D| over all pairs of B(6,2):", maxex)
    T6 = list(C(range(1, 7), 3))                                          # sec:gadget (why seven wires), six lines
    flip = lambda k, n: k[:n] + ("-" if k[n] == "+" else "+") + k[n + 1:]
    deficient = 0
    for a in keys6:
        for b, d in D6[a].items():
            h = sum(1 for x, y in zip(a, b) if x != y)
            if a < b and d > h:
                deficient += 1
                assert (h, d) == (16, 18)
                ports = [T6[n] for n in range(20) if a[n] == b[n] and flip(a, n) in idx6 and flip(b, n) in idx6
                         and D6[flip(a, n)][flip(b, n)] == h]
                assert len(ports) == 4 and all(len(set(P) & set(Q)) == 1 for P, Q in C(ports, 2))
    assert deficient == 16
    print("   the 16 pairs with d_B > |D| have |D|=16, d_B=18, and 4 ports each, pairwise meeting in one line")
    print("[11] sec:gadget (why seven wires)")
    found = check_unique(sig3[7])
    assert found == [("between", (5, 3, 2, 6, 7, 1))], found   # kappa: p meets w1,u3,u2,w2,w3,u1
    print("   the only cell with excess pattern (2,0,0,0):", found)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
