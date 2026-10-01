"""Braid-move-level checks (Part I in the language of words), complementing check.py, which works with sign vectors.

  [w1] lem:delete (deleting wires) on random reduced words, including braid moves on triples meeting A in two wires
  [w2] cor:edgeD(a): deleting all wires outside A_e turns W^s_G, W^v_G into the gadget words, for every edge
  [w3] prop:upper performed as actual braid moves (with commutation-class comparison after every factor)
  [w4] thm:rank3: the hypothesis n >= 3 is needed (walks from F_3(s_G) to -F_3(v_G) for G = 2K_1 and G = K_2)
"""
import sys, itertools, random
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as ck
C = itertools.combinations

def swaps(word, m):
    """list of pairs swapped, in order"""
    pos = list(range(1, m+1)); out = []
    for i in word:
        a, b = pos[i-1], pos[i]
        out.append((min(a,b), max(a,b)))
        pos[i-1], pos[i] = b, a
    return out

def restrict(word, m, A):
    """W|_A of lem:delete"""
    A = sorted(A); idx = {a: k+1 for k, a in enumerate(A)}
    pos = list(range(1, m+1)); out = []
    for i in word:
        a, b = pos[i-1], pos[i]
        if a in idx and b in idx:
            rel = [x for x in pos if x in idx]
            j = rel.index(a) + 1  # a is upper
            out.append(j)
        pos[i-1], pos[i] = b, a
    return out

def heap_less(word):
    """transitive closure of heap order: i<j and |w_i-w_j|<=1 generate"""
    n = len(word)
    less = [set() for _ in range(n)]  # less[j] = set of i <_P j
    for j in range(n):
        for i in range(j):
            if abs(word[i]-word[j]) <= 1:
                less[j].add(i); less[j] |= less[i]
    return less

def canon(word):
    """lex-min word in commutation class"""
    n = len(word); less = heap_less(word)
    used = [False]*n; out = []
    for _ in range(n):
        cands = [j for j in range(n) if not used[j] and all(used[i] for i in less[j])]
        j = min(cands, key=lambda j: (word[j], j))
        used[j] = True; out.append(word[j])
    return tuple(out)

def braid_flip(word, m, T):
    """If a word equivalent to `word` has the three swaps of T consecutive, return the word after the braid move; else None."""
    T = tuple(sorted(T))
    sw = swaps(word, m)
    ids = [k for k, p in enumerate(sw) if set(p) <= set(T)]
    assert len(ids) == 3
    i1, i2, i3 = ids
    less = heap_less(word)
    if not (i1 in less[i3]):
        return None
    for x in range(len(word)):
        if x in (i1, i2, i3): continue
        if i1 in less[x] and x in less[i3]:
            return None
    # up-set of i1
    up = {x for x in range(len(word)) if i1 in less[x]} | {i1}
    first = [x for x in range(len(word)) if x not in up]
    rest = [x for x in range(len(word)) if x in up and x not in (i1, i2, i3)]
    new = [word[x] for x in first] + [word[i1], word[i2], word[i3]] + [word[x] for x in rest]
    assert canon(new) == canon(word)
    a, b, c = word[i1], word[i2], word[i3]
    assert a == c and abs(a-b) == 1
    k = len(first)
    new[k:k+3] = [b, a, b]
    return new

def sig(word, m):
    return ck.sig_of_word(word, m)[0]

# ---------------------------------------------------------------- t1
# lem:delete random tests, braid-move behaviour
rng = random.Random(1)
def randword(m):
    word, pos = [], list(range(1, m + 1))
    while True:
        cand = [i for i in range(1, m) if pos[i - 1] < pos[i]]
        if not cand: return word
        i = rng.choice(cand); word.append(i); pos[i - 1], pos[i] = pos[i], pos[i - 1]
cnt = 0
for m in range(4, 9):
    for _ in range(200):
        W = randword(m); s = sig(W, m)
        for k in range(2, m+1):
            A = sorted(rng.sample(range(1, m+1), k))
            R = restrict(W, m, A)
            sr = ck.sig_of_word(R, k)[0]  # asserts reduced
            for T in C(range(1, k+1), 3):
                assert sr[T] == s[tuple(A[t-1] for t in T)]
            # commutation
            for i in range(len(W)-1):
                if abs(W[i]-W[i+1]) >= 2:
                    W2 = W[:i] + [W[i+1], W[i]] + W[i+2:]
                    assert canon(restrict(W2, m, A)) == canon(R)
            # braid moves
            for i in range(len(W)-2):
                if W[i] == W[i+2] and abs(W[i]-W[i+1]) == 1:
                    W2 = W[:i] + [W[i+1], W[i], W[i+1]] + W[i+3:]
                    T = set(swaps(W, m)[i]) | set(swaps(W, m)[i+1])
                    R2 = restrict(W2, m, A)
                    if T <= set(A):
                        # R2 arises from R by a braid move flipping T (literal)
                        diff = [j for j in range(len(R)) if R[j] != R2[j]]
                        assert len(diff) == 3 and diff[2]-diff[0] == 2, (R, R2)
                        cnt += 1
                    else:
                        assert R2 == R
print("lem:delete OK", cnt)

# ---------------------------------------------------------------- t2
# cor:edgeD(a) at word level
graphs = {"P2": (2, [(1, 2)]), "P3": (3, [(1, 2), (2, 3)]), "K3": (3, [(1, 2), (1, 3), (2, 3)]),
          "C4": (4, [(1, 2), (2, 3), (3, 4), (1, 4)]), "K4": (4, list(C(range(1, 5), 2))),
          "K13b": (4, [(1, 4), (2, 4), (3, 4)]), "K5": (5, list(C(range(1, 6), 2)))}
b1b5k = ck.bead(1,0)+ck.bead(5,0)+ck.KAPPA
kb1b5 = ck.KAPPA+ck.bead(1,0)+ck.bead(5,0)
kb5b1 = ck.KAPPA+ck.bead(5,0)+ck.bead(1,0)
for name,(n,es) in graphs.items():
    con = ck.construct(n, es); m = con["m"]; J = len(con["factors"])
    W0 = ck.word_with_beads(con, 0, {}); WJ = ck.word_with_beads(con, J, {})
    lit0 = litJ = 0
    for (u,w) in con["E"]:
        A = con["lines"][("X", u)] + con["lines"][("p", (u, w))] + con["lines"][("X", w)]
        R0 = restrict(W0, m, A); RJ = restrict(WJ, m, A)
        assert canon(R0) == canon(b1b5k) and canon(RJ) == canon(kb1b5)
        lit0 += (R0 == b1b5k); litJ += (RJ == kb1b5)
    # also check with beads in increasing-u order (the paper's product over u in [n])
    def wb(k):
        fs = con["factors"]; w = [x for f in fs[:k] for x in f["letters"]]
        pos = fs[k]["before"] if k < len(fs) else fs[-1]["after"]
        for u in sorted(pos): w += ck.bead(pos[u], 0)
        return w + [x for f in fs[k:] for x in f["letters"]]
    W0u, WJu = wb(0), wb(J)
    litJu = sum(restrict(WJu, m, con["lines"][("X", u)] + con["lines"][("p", (u, w))] + con["lines"][("X", w)]) == kb1b5 for (u,w) in con["E"])
    litJu5 = sum(restrict(WJu, m, con["lines"][("X", u)] + con["lines"][("p", (u, w))] + con["lines"][("X", w)]) == kb5b1 for (u,w) in con["E"])
    print(name, "edges", len(con["E"]), "literal W0:", lit0, "literal WJ (beads by position):", litJ,
          "| beads by increasing u: WJ==k b1 b5:", litJu, " WJ==k b5 b1:", litJu5)

# ---------------------------------------------------------------- t3
# braid-move realizations: the 32-flip walk walk, gadget tight walks, and the whole prop:upper sequence
S7 = list(range(1,8))
# the 32-flip walk
walk147 = ("147 167 157 156 247 267 257 256 467 367 457 357 347 456 245 145 356 235 135 125 346 234 134 124 "
           "236 136 126 146 237 137 127 147").split()
W = ck.bead(1,0)+ck.bead(5,0)+ck.KAPPA
for t in walk147:
    T = tuple(int(c) for c in t)
    W2 = braid_flip(W, 7, T)
    assert W2 is not None, t
    W = W2
assert canon(W) == canon(ck.KAPPA+ck.bead(1,0)+ck.bead(5,0))
print("the 32-flip walk walk realized by 32 braid moves")
for e in [(1,0),(0,1),(1,1)]:
    order = ck.gadget_cell_walk(e)
    W = ck.bead(1,e[0])+ck.bead(5,e[1])+ck.KAPPA
    for T in order:
        W = braid_flip(W, 7, T); assert W is not None
    assert canon(W) == canon(ck.KAPPA+ck.bead(1,e[1])+ck.bead(5,e[0]))
print("gadget tight walks realized by 30 braid moves")

def upper_braid(con, cover):
    m, L = con["m"], con["lines"]; S = list(range(1, m+1)); J = len(con["factors"])
    eps = {u: 1 for u in cover}
    W = ck.word_with_beads(con, 0, {}); nb = 0
    # phase 1: literal bead exchange must be one braid move
    for u in cover:
        T = tuple(L[("X", u)])
        W2 = braid_flip(W, m, T); assert W2 is not None; W = W2; nb += 1
    assert canon(W) == canon(ck.word_with_beads(con, 0, eps))
    cell_orders = {e: ck.gadget_cell_walk(e) for e in [(1, 0), (0, 1), (1, 1)]}
    for k, f in enumerate(con["factors"]):
        cur = sig(W, m)
        kind, ev = f["kind"], f["ev"]
        orders = []
        if kind in ("Xp", "pX"):
            X = L[ev[1]] if kind == "Xp" else L[ev[2]]
            z = L[ev[2]][0] if kind == "Xp" else L[ev[1]][0]
            orders = ck.tight_order(dict(cur), [tuple(sorted((a, b, z))) for a, b in C(X, 2)], S)
        elif kind == "XX":
            X, Y = L[ev[1]], L[ev[2]]; c2 = dict(cur)
            for y in sorted(Y, reverse=True):
                o = ck.tight_order(c2, [tuple(sorted((a, b, y))) for a, b in C(X, 2)], S); orders += o
            for x in sorted(X, reverse=True):
                o = ck.tight_order(c2, [tuple(sorted((x, a, b))) for a, b in C(Y, 2)], S); orders += o
        elif kind == "cell":
            _, Xu, p, Xw = ev; A = L[Xu] + L[p] + L[Xw]
            key = (eps.get(Xu[1], 0), eps.get(Xw[1], 0)); assert key != (0,0)
            orders = [tuple(A[i-1] for i in T) for T in cell_orders[key]]
        for T in orders:
            W2 = braid_flip(W, m, T); assert W2 is not None, (kind, T); W = W2; nb += 1
        assert canon(W) == canon(ck.word_with_beads(con, k+1, eps)), kind
    for u in cover:
        W2 = braid_flip(W, m, tuple(L[("X", u)])); assert W2 is not None; W = W2; nb += 1
    assert canon(W) == canon(ck.word_with_beads(con, J, {}))
    return nb
for name,(n,es) in {"P2": (2, [(1, 2)]), "P3": (3, [(1, 2), (2, 3)]), "K3": (3, [(1, 2), (1, 3), (2, 3)]),
                    "C4": (4, [(1, 2), (2, 3), (3, 4), (1, 4)]), "2K2": (4, [(1, 3), (2, 4)]),
                    "K13b": (4, [(1, 4), (2, 4), (3, 4)]), "P2+2K1": (4, [(2, 3)])}.items():
    con = ck.construct(n, es); m = con["m"]
    sG, vG = ck.sG_vG(con); Dn = sum(sG[T] != vG[T] for T in sG)
    covers = [c for k in range(n + 1) for c in C(range(1, n + 1), k) if all(a in c or b in c for a, b in con["E"])]
    for c in covers:
        nb = upper_braid(con, list(c)); assert nb == Dn + 2*len(c)
    print(name, "m", m, "|D|", Dn, "all", len(covers), "covers realized by braid moves")

# ---------------------------------------------------------------- t4
# Is d([F s_G],[F v_G]) = |D|+2VC for n <= 2?  Search for short walks from chi_s to -chi_v in the double cover.
sys.setrecursionlimit(10000)
def gp_ok_at(chi, B, E):
    for e in B:
        x, y = [t for t in B if t != e]
        others = [t for t in E if t not in B]
        for c, d in C(others, 2):
            a4 = sorted((x, y, c, d))
            a, b, cc, dd = a4
            v = lambda p, q: ck.chi_val(chi, (e, p, q))
            T = (v(a, b) * v(cc, dd), -v(a, cc) * v(b, dd), v(a, dd) * v(b, cc))
            if T[0] == T[1] == T[2]:
                return False
    return True

def tight_search(chi0, target, E, extra=0):
    """DFS for a walk of length |D|+2*extra (extra detours allowed on bases outside D only once each is not enforced)."""
    D0 = [B for B in chi0 if chi0[B] != target[B]]
    seen = set()
    cur = dict(chi0)
    def key(): return tuple(cur[B] for B in sorted(cur))
    def rec(budget):
        d = [B for B in cur if cur[B] != target[B]]
        if not d: return []
        if len(d) > budget: return None
        k = (key(), budget)
        if k in seen: return None
        seen.add(k)
        cand = d + ([B for B in cur if cur[B] == target[B]] if budget > len(d) else [])
        for B in cand:
            cur[B] = -cur[B]
            if gp_ok_at(cur, B, E):
                r = rec(budget - 1)
                if r is not None:
                    cur[B] = -cur[B]; return [B] + r
            cur[B] = -cur[B]
        return None
    return len(D0), rec(len(D0) + 2*extra)

for name, (n, es) in {"2K1": (2, []), "P2": (2, [(1, 2)])}.items():
    con = ck.construct(n, es); m = con["m"]
    sG, vG = ck.sG_vG(con)
    S = list(range(1, m+1)); E = S + [ck.INF]
    chs, chv = ck.F(sG, S, 3), ck.F(vG, S, 3)
    assert ck.is_chirotope(chs, E, 3) and ck.is_chirotope(chv, E, 3)
    neg = {B: -chv[B] for B in chv}
    Dn = sum(sG[T] != vG[T] for T in sG)
    print(name, "m", m, "|D|", Dn, "claimed", Dn + 2*len(es and [1]))
    h, path = tight_search(chs, neg, E, 0)
    print("   Hamming(chi_s, -chi_v) =", h, "; tight walk found:", path is not None)
    if path is not None:
        cur = dict(chs)
        for B in path:
            cur[B] = -cur[B]; assert ck.is_chirotope(cur, E, 3)
        assert cur == neg
        print("   verified walk of length", len(path), "from chi_s to -chi_v")

print("ALL WORD-LEVEL CHECKS PASSED")
