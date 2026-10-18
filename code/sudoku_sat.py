#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sudoku_sat.py -- SAT encodings for (generalised) N x N Sudoku, N = n^2.

Contents
  * Five AMO (at-most-one) encoders: pairwise, sequential counter, binary,
    commander, product (all implemented here, no external dependency).
  * Minimal / extended CNF encodings of Sudoku (Lynce & Ouaknine style).
  * Closed-form size formulas + a streaming clause counter, so sizes of CNFs
    that are too big to store (e.g. N = 100) can still be reported.
  * Independent solution checker, puzzle generator, DIMACS writer.
  * A tiny reference DPLL solver used ONLY for validation/testing.
    Real experiments should use CDCL solvers (PySAT: cadical195, glucose4, ...).

CLI
  python sudoku_sat.py sizes   --out ../report          # size tables + figure
  python sudoku_sat.py verify  --out ../report          # correctness tests
  python sudoku_sat.py solve   --puzzle <81 chars> --amo seq --variant minimal
  python sudoku_sat.py gen     --n 4 --holes 0.5 --seed 1
  python sudoku_sat.py dimacs  --puzzle <81 chars> --out puzzle.cnf
"""
import argparse, itertools, json, math, os, random, sys, time

# ----------------------------------------------------------------------------
# 1. Clause sinks and variable pool
# ----------------------------------------------------------------------------
class Pool:
    """Allocates fresh auxiliary variables above the primary ones."""
    def __init__(self, top): self.top = top
    def new(self):
        self.top += 1
        return self.top

class ListSink:
    """Stores clauses (use for N <= ~25 with pairwise)."""
    def __init__(self): self.clauses = []
    def add(self, c): self.clauses.append(c)
    @property
    def n(self): return len(self.clauses)
    @property
    def lits(self): return sum(len(c) for c in self.clauses)

class CountSink:
    """Only counts clauses/literals (streaming, O(1) memory)."""
    def __init__(self): self.n = 0; self.lits = 0
    def add(self, c): self.n += 1; self.lits += len(c)

# ----------------------------------------------------------------------------
# 2. AMO encoders:  f(lits, pool, sink)
# ----------------------------------------------------------------------------
def amo_pairwise(lits, pool, sink):
    for a, b in itertools.combinations(lits, 2):
        sink.add([-a, -b])

def amo_seqcounter(lits, pool, sink):
    """Sinz (2005), k = 1:  m-1 aux variables, 3m-4 clauses."""
    m = len(lits)
    if m < 2: return
    s = [pool.new() for _ in range(m - 1)]        # s[i]: some x_j (j<=i) is true
    sink.add([-lits[0], s[0]])
    for i in range(1, m - 1):
        sink.add([-lits[i], s[i]])
        sink.add([-s[i - 1], s[i]])
        sink.add([-lits[i], -s[i - 1]])
    sink.add([-lits[m - 1], -s[m - 2]])

def amo_binary(lits, pool, sink):
    """Binary / bitwise: ceil(log2 m) aux variables, m*ceil(log2 m) clauses."""
    m = len(lits)
    if m < 2: return
    k = (m - 1).bit_length()
    y = [pool.new() for _ in range(k)]
    for i, x in enumerate(lits):
        for j in range(k):
            sink.add([-x, y[j] if (i >> j) & 1 else -y[j]])

def partition_sizes(m, g):
    base, rem = divmod(m, g)
    return [base + 1] * rem + [base] * (g - rem)

def amo_commander(lits, pool, sink, s=3):
    """Commander encoding (Klieber & Kwon), one level, groups of size ~s,
    commander c_i <-> (OR of group i), pairwise AMO inside groups and on the c_i."""
    m = len(lits)
    if m < 2: return
    g = -(-m // s)
    groups, pos = [], 0
    for sz in partition_sizes(m, g):
        groups.append(lits[pos:pos + sz]); pos += sz
    c = [pool.new() for _ in groups]
    for a, b in itertools.combinations(c, 2): sink.add([-a, -b])
    for ci, G in zip(c, groups):
        sink.add([-ci] + list(G))                       # c_i -> OR(G_i)
        for a, b in itertools.combinations(G, 2): sink.add([-a, -b])
        for x in G: sink.add([-x, ci])                  # x -> c_i

def ceil_sqrt(m):
    p = math.isqrt(m)
    return p if p * p >= m else p + 1

def amo_product(lits, pool, sink):
    """Product encoding (Chen 2010), one level: p x q grid, p=ceil(sqrt m),
    q=ceil(m/p); AMO(rows) and AMO(cols) pairwise; x_i -> r_u and x_i -> c_v."""
    m = len(lits)
    if m < 2: return
    p = ceil_sqrt(m); q = -(-m // p)
    r = [pool.new() for _ in range(p)]
    c = [pool.new() for _ in range(q)]
    for a, b in itertools.combinations(r, 2): sink.add([-a, -b])
    for a, b in itertools.combinations(c, 2): sink.add([-a, -b])
    for i, x in enumerate(lits):
        sink.add([-x, r[i // q]]); sink.add([-x, c[i % q]])

AMO = {"pairwise": amo_pairwise, "seq": amo_seqcounter, "binary": amo_binary,
       "commander": amo_commander, "product": amo_product}
AMO_LABEL = {"pairwise": "Pairwise", "seq": "Sequential", "binary": "Binary",
             "commander": "Commander", "product": "Product"}

def amo_cost(kind, m, s=3):
    """Closed form (aux variables, clauses) of AMO over m >= 2 literals."""
    if m < 2: return 0, 0
    if kind == "pairwise": return 0, m * (m - 1) // 2
    if kind == "seq":      return m - 1, 3 * m - 4
    if kind == "binary":
        k = (m - 1).bit_length(); return k, m * k
    if kind == "commander":
        g = -(-m // s); sz = partition_sizes(m, g)
        return g, g * (g - 1) // 2 + g + m + sum(z * (z - 1) // 2 for z in sz)
    if kind == "product":
        p = ceil_sqrt(m); q = -(-m // p)
        return p + q, 2 * m + p * (p - 1) // 2 + q * (q - 1) // 2
    raise ValueError(kind)

# ----------------------------------------------------------------------------
# 3. Sudoku CNF
# ----------------------------------------------------------------------------
def var(n, r, c, d):
    """DIMACS id of x_{r,c,d}; r,c,d are 0-based (digit d means d+1)."""
    N = n * n
    return (r * N + c) * N + d + 1

def box_cells(n, b):
    br, bc = divmod(b, n)
    return [(br * n + i, bc * n + j) for i in range(n) for j in range(n)]

def encode(n, amo="pairwise", variant="minimal", clues=None, sink=None, s=3):
    """Return (sink, num_vars).  clues: {(r,c): digit(1..N)}."""
    N = n * n
    pool, sink = Pool(N ** 3), (sink if sink is not None else ListSink())
    f = AMO[amo]
    def AMO_(lits):
        if amo == "commander": f(lits, pool, sink, s)
        else: f(lits, pool, sink)
    ext = (variant == "extended")
    # (C1) every cell has at least one digit
    for r in range(N):
        for c in range(N):
            sink.add([var(n, r, c, d) for d in range(N)])
    # (C2) at most one digit per cell            [extended only]
    if ext:
        for r in range(N):
            for c in range(N):
                AMO_([var(n, r, c, d) for d in range(N)])
    # (C3) rows, (C4) columns, (C5) boxes: AMO (+ ALO in the extended variant)
    for d in range(N):
        for r in range(N):
            g = [var(n, r, c, d) for c in range(N)]
            AMO_(g)
            if ext: sink.add(g)
        for c in range(N):
            g = [var(n, r, c, d) for r in range(N)]
            AMO_(g)
            if ext: sink.add(g)
        for b in range(N):
            g = [var(n, r, c, d) for (r, c) in box_cells(n, b)]
            AMO_(g)
            if ext: sink.add(g)
    # (C6) clues
    for (r, c), d in (clues or {}).items():
        sink.add([var(n, r, c, d - 1)])
    return sink, pool.top

def formula_size(n, amo, variant, n_clues=0, s=3):
    """Closed-form (variables, clauses) of the Sudoku CNF."""
    N = n * n
    a, cl = amo_cost(amo, N, s)
    if variant == "minimal":
        return N ** 3 + 3 * N * N * a, N * N + 3 * N * N * cl + n_clues
    return N ** 3 + 4 * N * N * a, 4 * N * N + 4 * N * N * cl + n_clues

def decode(n, model_true):
    """model_true: iterable of true DIMACS ids. Returns N x N grid (1..N)."""
    N = n * n
    grid = [[0] * N for _ in range(N)]
    for v in model_true:
        if 1 <= v <= N ** 3:
            r, rest = divmod(v - 1, N * N); c, d = divmod(rest, N)
            if grid[r][c] != 0: raise ValueError("cell has two digits")
            grid[r][c] = d + 1
    return grid

def is_valid_solution(n, grid, clues=None):
    N = n * n
    full = set(range(1, N + 1))
    if len(grid) != N or any(len(row) != N for row in grid): return False
    for i in range(N):
        if set(grid[i]) != full: return False
        if {grid[r][i] for r in range(N)} != full: return False
        if {grid[r][c] for r, c in box_cells(n, i)} != full: return False
    return all(grid[r][c] == d for (r, c), d in (clues or {}).items())

# ----------------------------------------------------------------------------
# 4. Puzzles: parsing, formatting, generation
# ----------------------------------------------------------------------------
def parse_puzzle(text, N):
    toks = text.split()
    if len(toks) == 1 and len(toks[0]) == N * N and N <= 9:
        vals = [0 if ch in ".0" else int(ch) for ch in toks[0]]
    else:
        vals = [int(t) for t in toks]
    if len(vals) != N * N: raise ValueError("bad puzzle length")
    return {(i // N, i % N): v for i, v in enumerate(vals) if v}

def format_grid(grid):
    return "\n".join(" ".join(f"{v:2d}" for v in row) for row in grid)

def random_complete_grid(n, rng):
    N = n * n
    base = [[(n * (r % n) + r // n + c) % N for c in range(N)] for r in range(N)]
    digits = list(range(N)); rng.shuffle(digits)
    def order():
        g = list(range(n)); rng.shuffle(g)
        return [gi * n + ri for gi in g for ri in rng.sample(range(n), n)]
    rows, cols = order(), order()
    return [[digits[base[r][c]] + 1 for c in cols] for r in rows]

def make_puzzle(n, hole_ratio, rng):
    N = n * n
    sol = random_complete_grid(n, rng)
    cells = [(r, c) for r in range(N) for c in range(N)]
    holes = set(rng.sample(cells, int(round(hole_ratio * N * N))))
    return {(r, c): sol[r][c] for (r, c) in cells if (r, c) not in holes}, sol

# ----------------------------------------------------------------------------
# 5. Reference solver (testing only): DPLL, watched literals, MRV branching
# ----------------------------------------------------------------------------
def dpll_solve(clauses, nvars, assumptions=(), branch_clauses=None):
    """Return assignment list (index 1..nvars, +1/-1) or None if UNSAT."""
    assign = [0] * (nvars + 1); trail = []
    watches = [[] for _ in range(2 * nvars + 2)]
    li = lambda l: 2 * l if l > 0 else -2 * l + 1
    cls, units = [], []
    for c in clauses:
        c = list(dict.fromkeys(c))
        if any(-l in c for l in c): continue
        if not c: return None
        if len(c) == 1: units.append(c[0]); continue
        cls.append(c); watches[li(c[0])].append(len(cls) - 1); watches[li(c[1])].append(len(cls) - 1)
    qh = 0
    def enqueue(l):
        v, want = abs(l), (1 if l > 0 else -1)
        if assign[v] == 0: assign[v] = want; trail.append(l); return True
        return assign[v] == want
    def propagate():
        nonlocal qh
        while qh < len(trail):
            fl = -trail[qh]; qh += 1
            ws = watches[li(fl)]; i = j = 0; n = len(ws)
            while i < n:
                ci = ws[i]; i += 1; c = cls[ci]
                if c[0] == fl: c[0], c[1] = c[1], c[0]
                a0 = c[0]; v0 = assign[abs(a0)]
                if v0 == (1 if a0 > 0 else -1): ws[j] = ci; j += 1; continue
                for k in range(2, len(c)):
                    lk = c[k]
                    if assign[abs(lk)] != (-1 if lk > 0 else 1):
                        c[1], c[k] = c[k], c[1]; watches[li(c[1])].append(ci); break
                else:
                    ws[j] = ci; j += 1
                    if v0 == (-1 if a0 > 0 else 1):
                        while i < n: ws[j] = ws[i]; j += 1; i += 1
                        del ws[j:]; return False
                    enqueue(a0)
            del ws[j:]
        return True
    def pick():
        best, bn = 0, 10 ** 9
        for bc in (branch_clauses or ()):
            cnt, first, sat = 0, 0, False
            for l in bc:
                v = assign[abs(l)]
                if v == 0:
                    cnt += 1
                    if not first: first = l
                elif (v > 0) == (l > 0): sat = True; break
            if not sat and cnt < bn:
                bn, best = cnt, first
                if cnt <= 2: break
        if best: return best
        for v in range(1, nvars + 1):
            if assign[v] == 0: return -v
        return 0
    for u in list(units) + list(assumptions):
        if not enqueue(u): return None
    if not propagate(): return None
    stack = []
    while True:
        lit = pick()
        if lit == 0: return assign
        stack.append((len(trail), lit, False)); enqueue(lit)
        conflict = not propagate()
        while conflict:
            if not stack: return None
            tl, l, flipped = stack.pop()
            for x in trail[tl:]: assign[abs(x)] = 0
            del trail[tl:]; qh = tl
            if flipped: continue
            stack.append((tl, -l, True)); enqueue(-l); conflict = not propagate()

def unit_propagate(clauses, assumptions):
    """Naive UP fix-point. Returns (conflict?, {var: bool})."""
    val = {}
    for a in assumptions:
        if val.get(abs(a), a > 0) != (a > 0): return True, val
        val[abs(a)] = a > 0
    changed = True
    while changed:
        changed = False
        for c in clauses:
            unassigned, sat = [], False
            for l in c:
                v = val.get(abs(l))
                if v is None: unassigned.append(l)
                elif v == (l > 0): sat = True; break
            if sat: continue
            if not unassigned: return True, val
            if len(unassigned) == 1:
                l = unassigned[0]; val[abs(l)] = l > 0; changed = True
    return False, val

def solve_dpll(n, amo="pairwise", variant="minimal", clues=None):
    N = n * n
    sink, nv = encode(n, amo, variant, clues)
    alo = [c for c in sink.clauses if len(c) == N and all(l > 0 for l in c)]
    m = dpll_solve(sink.clauses, nv, branch_clauses=alo)
    if m is None: return None
    return decode(n, [v for v in range(1, nv + 1) if m[v] > 0])

# ---- wrapper for a real CDCL solver (NOT exercised in the sandbox that built this file)
def solve_pysat(n, amo="seq", variant="minimal", clues=None, solver="cadical195"):
    """Requires `pip install python-sat`. Solver names: cadical195, glucose4, minisat22 ..."""
    from pysat.solvers import Solver
    sink, nv = encode(n, amo, variant, clues)
    with Solver(name=solver, bootstrap_with=sink.clauses) as s:
        if not s.solve(): return None
        return decode(n, [l for l in s.get_model() if l > 0])

def write_dimacs(path, clauses, nvars):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses: f.write(" ".join(map(str, c)) + " 0\n")

# ----------------------------------------------------------------------------
# 6. Validation suite
# ----------------------------------------------------------------------------
def amo_instance(kind, m):
    pool = Pool(m); sink = ListSink(); lits = list(range(1, m + 1))
    if kind == "commander": amo_commander(lits, pool, sink, 3)
    else: AMO[kind](lits, pool, sink)
    return sink.clauses, pool.top

def test_amo_exhaustive(kind, m):
    """For every assignment of the m primary variables: SAT iff <= 1 true."""
    cl, nv = amo_instance(kind, m); cases = 0
    for bits in itertools.product([False, True], repeat=m):
        ass = [(i + 1) if b else -(i + 1) for i, b in enumerate(bits)]
        res = dpll_solve(cl, nv, assumptions=ass) is not None
        if res != (sum(bits) <= 1): return cases, False
        cases += 1
    return cases, True

def test_amo_low_weight(kind, m):
    """All assignments with 0, 1 or 2 true primary variables."""
    cl, nv = amo_instance(kind, m); cases = 0
    for w in (0, 1, 2):
        for T in itertools.combinations(range(m), w):
            ass = [(i + 1) if i in T else -(i + 1) for i in range(m)]
            if (dpll_solve(cl, nv, assumptions=ass) is not None) != (w <= 1): return cases, False
            cases += 1
    return cases, True

def test_up_property(kind, m):
    """Asserting x_i = true makes UP derive not x_j for every j != i, no conflict."""
    cl, nv = amo_instance(kind, m); cases = 0
    for i in range(1, m + 1):
        conflict, val = unit_propagate(cl, [i])
        if conflict or any(val.get(j) is not False for j in range(1, m + 1) if j != i): return cases, False
        cases += 1
    return cases, True

def test_sizes(n, kind, variant):
    sink = CountSink(); _, nv = encode(n, kind, variant, None, sink)
    fv, fc = formula_size(n, kind, variant)
    return (nv == fv and sink.n == fc), (nv, sink.n, fv, fc)

WIKI = ("530070000" "600195000" "098000060" "800060003" "400803001"
        "700020006" "060000280" "000419005" "000080079")
WIKI_SOL = ("534678912" "672195348" "198342567" "859761423" "426853791"
            "713924856" "961537284" "287419635" "345286179")

def cmd_verify(a):
    out = {"amo_exhaustive": {}, "amo_low_weight": {}, "up": {}, "sizes": {}, "sudoku": {}}
    t0 = time.time(); kinds = list(AMO)
    for k in kinds:
        tot, ok = 0, True
        for m in range(1, 11):
            c, o = test_amo_exhaustive(k, m); tot += c; ok &= o
        out["amo_exhaustive"][k] = {"cases": tot, "ok": ok}
        tot, ok = 0, True
        for m in range(11, 25):
            c, o = test_amo_low_weight(k, m); tot += c; ok &= o
        out["amo_low_weight"][k] = {"cases": tot, "ok": ok}
        tot, ok = 0, True
        for m in range(2, 65):
            c, o = test_up_property(k, m); tot += c; ok &= o
        out["up"][k] = {"cases": tot, "ok": ok}
        ok = True
        for m in range(2, 201):
            cl, nv = amo_instance(k, m)
            av, ac = amo_cost(k, m)
            ok &= (nv - m == av and len(cl) == ac)
        out["amo_exhaustive"][k]["formula_m2_200"] = ok
    print("AMO tests done in %.1fs" % (time.time() - t0))
    # Sudoku size formulas vs generator
    tot, ok = 0, True
    for n in (2, 3, 4, 5, 6, 7):
        for k in kinds:
            for v in ("minimal", "extended"):
                o, info = test_sizes(n, k, v); tot += 1; ok &= o
                if not o: print("SIZE MISMATCH", n, k, v, info)
    out["sizes"] = {"combinations": tot, "ok": ok, "N_max": 49}
    # Sudoku cross-check on the Wikipedia puzzle, all 10 configurations
    clues = parse_puzzle(WIKI, 9); ref = [[int(ch) for ch in WIKI_SOL[9 * r:9 * r + 9]] for r in range(9)]
    res = {}
    for k in kinds:
        for v in ("minimal", "extended"):
            t = time.time(); g = solve_dpll(3, k, v, clues)
            res[f"{k}/{v}"] = {"valid": bool(g and is_valid_solution(3, g, clues)),
                               "equals_reference": g == ref, "sec": round(time.time() - t, 2)}
    out["sudoku"]["wikipedia_9x9"] = res
    # uniqueness through a blocking clause
    sink, nv = encode(3, "seq", "minimal", clues)
    sink.add([-var(3, r, c, ref[r][c] - 1) for r in range(9) for c in range(9) if (r, c) not in clues])
    out["sudoku"]["unique"] = dpll_solve(sink.clauses, nv) is None
    # empty 4x4: satisfiable; contradictory clues: unsat
    g4 = solve_dpll(2, "pairwise", "minimal", {})
    out["sudoku"]["empty_4x4_valid"] = bool(g4 and is_valid_solution(2, g4))
    out["sudoku"]["conflicting_clues_unsat"] = solve_dpll(3, "seq", "minimal", {(0, 0): 5, (0, 1): 5}) is None
    # random generated instances (satisfiable by construction)
    rng = random.Random(2026); gen = {}
    for n, h in ((2, 0.5), (3, 0.5), (4, 0.4)):
        okc, cnt = 0, 0
        for _ in range(5):
            cl, _s = make_puzzle(n, h, rng); cnt += 1
            g = solve_dpll(n, "seq", "extended", cl); okc += bool(g and is_valid_solution(n, g, cl))
        gen[f"N={n*n},holes={h}"] = f"{okc}/{cnt}"
    out["sudoku"]["generated"] = gen
    out["seconds"] = round(time.time() - t0, 1)
    path = os.path.join(a.out, "results", "validation.json")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    json.dump(out, open(path, "w"), indent=1)
    print(json.dumps(out, indent=1))
    allok = (all(v["ok"] and v["formula_m2_200"] for v in out["amo_exhaustive"].values()) and
             all(v["ok"] for v in out["amo_low_weight"].values()) and all(v["ok"] for v in out["up"].values()) and
             out["sizes"]["ok"] and all(x["valid"] and x["equals_reference"] for x in res.values()) and
             out["sudoku"]["unique"] and out["sudoku"]["empty_4x4_valid"] and out["sudoku"]["conflicting_clues_unsat"])
    print("ALL TESTS PASSED" if allok else "SOME TESTS FAILED")
    return 0 if allok else 1

# ----------------------------------------------------------------------------
# 7. Size tables / figure for the report
# ----------------------------------------------------------------------------
def thin(x): return f"{x:,}".replace(",", "\\,")

def cmd_sizes(a):
    kinds = list(AMO); ns = [3, 4, 5, 6, 7, 8, 10]; Ns = [n * n for n in ns]
    rows = []
    for n in ns:
        for v in ("minimal", "extended"):
            for k in kinds:
                nv, nc = formula_size(n, k, v)
                rows.append({"n": n, "N": n * n, "variant": v, "amo": k, "vars": nv, "clauses": nc})
    tdir = os.path.join(a.out, "tables"); os.makedirs(tdir, exist_ok=True)
    os.makedirs(os.path.join(a.out, "results"), exist_ok=True)
    with open(os.path.join(a.out, "results", "encoding_sizes.csv"), "w") as f:
        f.write("n,N,variant,amo,vars,clauses\n")
        for r in rows: f.write(f"{r['n']},{r['N']},{r['variant']},{r['amo']},{r['vars']},{r['clauses']}\n")
    def table(name, variant, key):
        L = ["\\begin{tabular}{r" + "r" * len(kinds) + "}", "\\toprule",
             "$N$ & " + " & ".join(AMO_LABEL[k] for k in kinds) + " \\\\", "\\midrule"]
        for n in ns:
            vals = {r["amo"]: r[key] for r in rows if r["n"] == n and r["variant"] == variant}
            best = min(vals.values())
            cells = [("\\textbf{%s}" % thin(vals[k])) if vals[k] == best else thin(vals[k]) for k in kinds]
            L.append(f"{n*n} & " + " & ".join(cells) + " \\\\")
        L += ["\\bottomrule", "\\end{tabular}"]
        open(os.path.join(tdir, name), "w").write("\n".join(L) + "\n")
    table("size_vars_min.tex", "minimal", "vars");  table("size_cls_min.tex", "minimal", "clauses")
    table("size_vars_ext.tex", "extended", "vars"); table("size_cls_ext.tex", "extended", "clauses")
    # per-group table
    ms = [9, 16, 25, 64]
    L = ["\\begin{tabular}{lllcccc}", "\\toprule",
         "Encoding AMO & Số biến phụ & Số mệnh đề & " + " & ".join(f"$m={m}$" for m in ms) + " \\\\", "\\midrule"]
    form = {"pairwise": ("$0$", "$m(m-1)/2$"), "seq": ("$m-1$", "$3m-4$"),
            "binary": ("$\\lceil\\log_2 m\\rceil$", "$m\\lceil\\log_2 m\\rceil$"),
            "commander": ("$g=\\lceil m/3\\rceil$", "$\\binom{g}{2}+g+m+\\sum_i\\binom{s_i}{2}$"),
            "product": ("$p+q$", "$2m+\\binom{p}{2}+\\binom{q}{2}$")}
    for k in kinds:
        cells = [f"{amo_cost(k, m)[0]}\\,/\\,{amo_cost(k, m)[1]}" for m in ms]
        L.append(f"{AMO_LABEL[k]} & {form[k][0]} & {form[k][1]} & " + " & ".join(cells) + " \\\\")
    L += ["\\bottomrule", "\\end{tabular}"]
    open(os.path.join(tdir, "amo_group_sizes.tex"), "w").write("\n".join(L) + "\n")
    # figure
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size": 8, "font.family": "serif"})
    fig, axs = plt.subplots(1, 2, figsize=(6.6, 2.7))
    mk = {"pairwise": "o", "seq": "s", "binary": "^", "commander": "D", "product": "v"}
    for ax, key, ttl in ((axs[0], "vars", "(a) số biến"), (axs[1], "clauses", "(b) số mệnh đề (clause)")):
        for k in kinds:
            ax.plot(Ns, [r[key] for n in ns for r in rows if r["n"] == n and r["variant"] == "minimal" and r["amo"] == k],
                    marker=mk[k], ms=3.5, lw=1, label=AMO_LABEL[k])
        ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlabel("Kích thước lưới $N$"); ax.set_title(ttl, fontsize=8)
        ax.set_xticks(Ns); ax.set_xticklabels([str(x) for x in Ns], rotation=45); ax.minorticks_off(); ax.grid(alpha=.3)
    axs[0].legend(fontsize=6.5, frameon=False)
    plt.tight_layout()
    os.makedirs(os.path.join(a.out, "figures"), exist_ok=True)
    plt.savefig(os.path.join(a.out, "figures", "encoding_size.pdf")); plt.close()
    print("wrote tables/size_*.tex, tables/amo_group_sizes.tex, figures/encoding_size.pdf, results/encoding_sizes.csv")
    for r in rows:
        if r["N"] in (9, 16, 100) and r["variant"] == "minimal": print(r)

# ----------------------------------------------------------------------------
# 8. CLI
# ----------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    for name in ("sizes", "verify"):
        p = sp.add_parser(name); p.add_argument("--out", default="../report")
    p = sp.add_parser("solve"); p.add_argument("--puzzle", required=True); p.add_argument("--n", type=int, default=3)
    p.add_argument("--amo", default="seq", choices=list(AMO)); p.add_argument("--variant", default="minimal", choices=["minimal", "extended"])
    p.add_argument("--solver", default="dpll", help="dpll (reference) or a PySAT name, e.g. cadical195")
    p = sp.add_parser("gen"); p.add_argument("--n", type=int, default=3); p.add_argument("--holes", type=float, default=0.5); p.add_argument("--seed", type=int, default=0)
    p = sp.add_parser("dimacs"); p.add_argument("--puzzle", required=True); p.add_argument("--n", type=int, default=3)
    p.add_argument("--amo", default="seq", choices=list(AMO)); p.add_argument("--variant", default="minimal", choices=["minimal", "extended"]); p.add_argument("--out", required=True)
    a = ap.parse_args(argv)
    if a.cmd == "sizes": return cmd_sizes(a)
    if a.cmd == "verify": return cmd_verify(a)
    if a.cmd == "gen":
        cl, sol = make_puzzle(a.n, a.holes, random.Random(a.seed)); N = a.n ** 2
        print(" ".join(str(cl.get((r, c), 0)) for r in range(N) for c in range(N))); return 0
    N = a.n ** 2; clues = parse_puzzle(a.puzzle, N)
    if a.cmd == "dimacs":
        sink, nv = encode(a.n, a.amo, a.variant, clues); write_dimacs(a.out, sink.clauses, nv)
        print(f"wrote {a.out}: {nv} vars, {sink.n} clauses"); return 0
    t = time.time()
    g = solve_dpll(a.n, a.amo, a.variant, clues) if a.solver == "dpll" else solve_pysat(a.n, a.amo, a.variant, clues, a.solver)
    print(format_grid(g) if g else "UNSAT"); print(f"{time.time()-t:.2f}s")
    return 0

if __name__ == "__main__":
    sys.exit(main())
