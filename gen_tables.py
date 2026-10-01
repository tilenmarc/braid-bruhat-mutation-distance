"""Generate the figures of the paper (imports check.py): fig_gs.tex, fig_gv.tex, fig_p3_phi.tex, fig_p3_blowup.tex,
fig_p3_blowup_v.tex."""
from check import bead, KAPPA, construct, word_with_beads, sig_of_word, sG_vG

def tikz_wiring(word, m=7, fname="fig.tex", colors=None, marks=()):
    """TikZ wiring diagram: wire k starts at position k (top); letter s_i swaps positions i, i+1."""
    pos = list(range(1, m + 1))                 # pos[j] = wire at position j+1
    path = {w: [(0, m + 1 - w)] for w in range(1, m + 1)}
    x = 0
    for i in word:
        for j, w in enumerate(pos):
            y = m - j
            if j == i - 1:
                path[w].append((x + 1, m - (j + 1)))
            elif j == i:
                path[w].append((x + 1, m - (j - 1)))
            else:
                path[w].append((x + 1, y))
        pos[i - 1], pos[i] = pos[i], pos[i - 1]
        x += 1
    lines = [r"\begin{tikzpicture}[x=0.42cm,y=0.42cm]"]
    for (a, b, lab) in marks:
        lines.append(rf"\fill[black!7] ({a},0.55) rectangle ({b},{m}+0.45); \node[font=\scriptsize] at ({(a+b)/2},{m}+0.9) {{{lab}}};")
    for w, pts in path.items():
        col = colors(w) if colors else "black"
        lines.append(rf"\draw[{col},thick] " + " -- ".join(f"({px},{py})" for px, py in pts) + ";")
        lines.append(rf"\node[left,font=\scriptsize] at (0,{pts[0][1]}) {{{w}}};")
        lines.append(rf"\node[right,font=\scriptsize] at ({pts[-1][0]},{pts[-1][1]}) {{{w}}};")
    lines.append(r"\end{tikzpicture}")
    open(fname, "w").write("\n".join(lines) + "\n")

col = lambda w: "blue!70!black" if w <= 3 else ("black" if w == 4 else "red!70!black")
tikz_wiring(bead(1, 0) + bead(5, 0) + KAPPA, fname="fig_gs.tex", colors=col,
            marks=[(0, 3, r"$\beta_1$"), (3, 6, r"$\beta_5$")])
tikz_wiring(KAPPA + bead(1, 0) + bead(5, 0), fname="fig_gv.tex", colors=col,
            marks=[(15, 18, r"$\beta_1$"), (18, 21, r"$\beta_5$")])
print("gadget figures written")

# ---------------------------------------------------------------- figure: the construction for P_3

def tikz_general(word, names, fname, colors, marks=(), xs=0.42, ys=0.42, lw="thick"):
    m = len(names)
    pos = list(range(m))                 # pos[j] = index of the wire at position j+1
    path = {w: [(0, m - 1 - w)] for w in range(m)}
    for x, i in enumerate(word):
        for j, w in enumerate(pos):
            if j == i - 1:
                path[w].append((x + 1, m - (j + 1) - 1 + 1 - 1))
            elif j == i:
                path[w].append((x + 1, m - (j - 1) - 1))
            else:
                path[w].append((x + 1, m - j - 1))
        pos[i - 1], pos[i] = pos[i], pos[i - 1]
    lines = [rf"\begin{{tikzpicture}}[x={xs}cm,y={ys}cm]"]
    for (a, b, lab, shade) in marks:
        lines.append(rf"\fill[{shade}] ({a},-0.45) rectangle ({b},{m - 1}+0.45); \node[font=\scriptsize] at ({(a + b) / 2},{m - 1}+0.95) {{{lab}}};")
    for w, pts in path.items():
        lines.append(rf"\draw[{colors[w]},{lw}] " + " -- ".join(f"({px},{py})" for px, py in pts) + ";")
        lines.append(rf"\node[left,font=\scriptsize] at (0,{pts[0][1]}) {{{names[w]}}};")
        lines.append(rf"\node[right,font=\scriptsize] at ({pts[-1][0]},{pts[-1][1]}) {{{names[w]}}};")
    lines.append(r"\end{tikzpicture}")
    open(fname, "w").write("\n".join(lines) + "\n")

con = construct(3, [(1, 2), (2, 3)])
gcol = {("X", 1): "blue!70!black", ("X", 2): "red!70!black", ("X", 3): "green!50!black",
        ("p", (1, 2)): "black", ("p", (2, 3)): "black!55"}
gname = {("X", 1): "$X_1$", ("X", 2): "$X_2$", ("X", 3): "$X_3$", ("p", (1, 2)): "$p_{12}$", ("p", (2, 3)): "$p_{23}$"}
groups = con["groups"]
# group-level Phi: re-run the group events as letters on group positions
order = list(groups); gword = []; gmarks = []
for f in con["factors"]:
    ev = f["ev"]
    if ev[0] == "swap":
        i = order.index(ev[1]) + 1
        gword.append(i); order[i - 1], order[i] = order[i], order[i - 1]
    else:
        i = order.index(ev[1]) + 1
        start = len(gword)
        for l in (i + 1, i, i + 1):
            gword.append(l); order[l - 1], order[l] = order[l], order[l - 1]
        e = ev[2][1]
        gmarks.append((start, start + 3, f"cell $e={e[0]}{e[1]}$", "black!8"))
tikz_general(gword, [gname[g] for g in groups], "fig_p3_phi.tex", [gcol[g] for g in groups], gmarks, xs=0.9, ys=0.5)
# blow-up with beads first: the word W_0^0 of s_G
line_group = {}
for g in groups:
    for x in con["lines"][g]:
        line_group[x] = g
m = con["m"]
word = []
marks = [(0, 9, "beads", "black!8")]
for q in sorted(f for f in con["factors"][0]["before"].values()):
    word += bead(q, 0)
for f in con["factors"]:
    if f["kind"] == "cell":
        e = f["ev"][2][1]
        marks.append((len(word), len(word) + len(f["letters"]), rf"$\kappa$ of ${e[0]}{e[1]}$", "black!8"))
    word += f["letters"]
names = [str(x) for x in range(1, m + 1)]
colors = [gcol[line_group[x]] for x in range(1, m + 1)]
tikz_general(word, names, "fig_p3_blowup.tex", colors, marks, xs=0.27, ys=0.36)
# the same diagram with the beads at the end: the word W_J^0 of v_G
K = len(con["factors"])
wordv = word_with_beads(con, K, {})
marksv = []
x = 0
for f in con["factors"]:
    if f["kind"] == "cell":
        e = f["ev"][2][1]
        marksv.append((x, x + len(f["letters"]), rf"$\kappa$ of ${e[0]}{e[1]}$", "black!8"))
    x += len(f["letters"])
marksv.append((x, len(wordv), "beads", "black!8"))
sG, vG = sG_vG(con)
assert sig_of_word(word, m)[0] == sG and sig_of_word(wordv, m)[0] == vG
tikz_general(wordv, names, "fig_p3_blowup_v.tex", colors, marksv, xs=0.27, ys=0.36)
print("P3 figures written; Phi letters:", gword, "; W00 length", len(word), "; WJ0 length", len(wordv))


# ---------------------------------------------------------------- figure for Section 2: four wires
from check import sig_of_word
wcol = lambda w: {1: "blue!70!black", 2: "red!70!black", 3: "green!50!black", 4: "black"}[w]
W1 = [1, 2, 1, 3, 2, 1]          # sigma_1 sigma_2 sigma_1 sigma_3 sigma_2 sigma_1
W2 = [2, 1, 2, 3, 2, 1]          # after the braid move on the first three letters
s1, s2 = sig_of_word(W1, 4)[0], sig_of_word(W2, 4)[0]
assert [s1[T] for T in [(1,2,3),(1,2,4),(1,3,4),(2,3,4)]] == [1, 1, 1, 1]
assert [s2[T] for T in [(1,2,3),(1,2,4),(1,3,4),(2,3,4)]] == [-1, 1, 1, 1]
tikz_wiring(W1, m=4, fname="fig_w_a.tex", colors=wcol, marks=[(0, 3, r"$\sigma_1\sigma_2\sigma_1$")])
tikz_wiring(W2, m=4, fname="fig_w_b.tex", colors=wcol, marks=[(0, 3, r"$\sigma_2\sigma_1\sigma_2$")])
tikz_wiring([1, 2, 1], m=3, fname="fig_w_c.tex", colors=wcol)
print("Section 2 figures written")


# ---------------------------------------------------------------- figure: the word kappa, properties (K1)-(K3)
def tikz_kappa(fname="fig_kappa.tex", xs=0.62, ys=0.5):
    names = [r"$u_1$", r"$u_2$", r"$u_3$", r"$p$", r"$w_1$", r"$w_2$", r"$w_3$"]
    cols = ["blue!70!black"] * 3 + ["black"] + ["red!70!black"] * 3
    m = 7
    pos = list(range(m))                       # pos[j] = wire (0..6) at position j+1
    path = {w: [(0, m - 1 - w)] for w in range(m)}
    pcross, swaps = [], []
    for x, i in enumerate(KAPPA):
        a, b = pos[i - 1], pos[i]
        swaps.append(frozenset((a, b)))
        if 3 in (a, b):
            pcross.append((x + 0.5, m - i - 0.5, b if a == 3 else a))
        for j, w in enumerate(pos):
            if j == i - 1:
                path[w].append((x + 1, m - 1 - i))
            elif j == i:
                path[w].append((x + 1, m - i))
            else:
                path[w].append((x + 1, m - 1 - j))
        pos[i - 1], pos[i] = pos[i], pos[i - 1]
    group = lambda w: 0 if w < 3 else (1 if w == 3 else 2)
    # (K1) every pair from different groups exactly once, none inside a group
    assert len(set(swaps)) == len(swaps) == 15
    assert all(group(min(s)) != group(max(s)) for s in swaps)
    # (K2) final arrangement w1 w2 w3 p u1 u2 u3
    assert pos == [4, 5, 6, 3, 0, 1, 2]
    # (K3) p meets w1, u3, u2, w2, w3, u1
    assert [c[2] for c in pcross] == [4, 2, 1, 5, 6, 0]
    lines = [rf"\begin{{tikzpicture}}[x={xs}cm,y={ys}cm]"]
    for (a, b) in [(4, 6), (10, 14)]:          # shade every other factor
        lines.append(rf"\fill[black!6] ({a},-0.45) rectangle ({b},{m - 1}+0.45);")
    for w, pts in path.items():
        lines.append(rf"\draw[{cols[w]},thick] " + " -- ".join(f"({px},{py})" for px, py in pts) + ";")
        lines.append(rf"\node[left,font=\scriptsize] at (0,{pts[0][1]}) {{{names[w]}}};")
        lines.append(rf"\node[right,font=\scriptsize] at ({pts[-1][0]},{pts[-1][1]}) {{{names[w]}}};")
    for k, (px, py, _) in enumerate(pcross, 1):
        lines.append(rf"\node[circle,draw,fill=white,inner sep=0.6pt,font=\tiny] at ({px},{py}) {{{k}}};")
    labels = [(0, 4, r"$\sigma_4\sigma_3\sigma_2\sigma_1$"), (4, 6, r"$\sigma_4\sigma_3$"),
              (6, 10, r"$\sigma_5\sigma_4\sigma_3\sigma_2$"), (10, 14, r"$\sigma_6\sigma_5\sigma_4\sigma_3$"),
              (14, 15, r"$\sigma_4$")]
    for (a, b, lab) in labels:
        lines.append(rf"\node[font=\scriptsize] at ({(a + b) / 2},{m - 1}+1.0) {{{lab}}};")
    lines.append(r"\end{tikzpicture}")
    open(fname, "w").write("\n".join(lines) + "\n")


tikz_kappa()
print("kappa figure written; (K1)-(K3) checked")
