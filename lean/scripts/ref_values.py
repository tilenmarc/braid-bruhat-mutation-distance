"""Reference values from ../../check.py for the Lean sanity checks (labels shifted to 0-based)."""
import sys, os, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
import check as ck
C = itertools.combinations

def sstr(s, m):
    return "".join("+" if s[x] > 0 else "-" for x in C(range(1, m + 1), 3))

def info(n, edges):
    con = ck.construct(n, [(a + 1, b + 1) for a, b in edges])
    m = con["m"]
    sG, vG = ck.sG_vG(con)
    D = sum(sG[t] != vG[t] for t in sG)
    ws = ck.word_with_beads(con, 0, {})
    wv = ck.word_with_beads(con, len(con["factors"]), {})
    return dict(m=m, J=len(con["factors"]), D=D, s=sstr(sG, m), v=sstr(vG, m),
                ws=[x - 1 for x in ws], wv=[x - 1 for x in wv],
                kinds=[f["kind"] for f in con["factors"]])

if __name__ == "__main__":
    for name, n, edges in [("P3", 3, [(0, 1), (1, 2)]), ("K3", 3, [(0, 1), (0, 2), (1, 2)]),
                           ("K2", 2, [(0, 1)]), ("star", 4, [(0, 1), (0, 2), (0, 3)]),
                           ("2K1", 2, []), ("C4", 4, [(0, 1), (1, 2), (2, 3), (0, 3)])]:
        r = info(n, edges)
        print(name, "m", r["m"], "J", r["J"], "D", r["D"], "formula", 3 * n * (r["m"] - 3) + 6 * len(edges))
        print("  s", r["s"])
        print("  v", r["v"])
        print("  ws", r["ws"])
        print("  kinds", r["kinds"])
