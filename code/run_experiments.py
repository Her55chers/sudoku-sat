#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
run_experiments.py -- chay toan bo thuc nghiem va TU DIEN vao bao cao.

Lenh:
  python run_experiments.py check                       # xem solver nao dung duoc
      (them --cms DUONG_DAN neu dung file chay cryptominisat5 rieng)
  python run_experiments.py info --name "Nguyễn Văn A" --email x@vnu.edu.vn --github https://github.com/u/sudoku-sat
  python run_experiments.py run --profile quick         # chay thu (~1-3 gio)
  python run_experiments.py run --profile full          # chay day du (lau)
  python run_experiments.py report                      # chi tao lai bang/hinh/doan van tu ket qua da co
  python run_experiments.py reset                       # tra bao cao ve trang thai chu do

Ket qua duoc luu dan vao report/results/runs.csv, chay lai se BO QUA cac lan
da chay xong (co the dung giua chung roi chay tiep).
"""
import argparse, csv, json, os, platform, random, re, shutil, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sudoku_sat as S

ROOT = os.path.abspath(os.path.join(HERE, ".."))
REPORT = os.path.join(ROOT, "report")
INST = os.path.join(ROOT, "instances")
RUNS = os.path.join(REPORT, "results", "runs.csv")

AMOS = ["pairwise", "seq", "binary", "commander", "product"]
VARIANTS = ["minimal", "extended"]
SAT_SOLVERS = ["cadical195", "glucose4", "cms"]
SAT_LABEL = {"cadical195": "CaDiCaL", "glucose4": "Glucose",
             "cms": "CryptoMiniSat", "dpll": "DPLL (tham chiếu)"}

PROFILES = {
    # n = canh khoi (N = n*n)
    "smoke": dict(time_limit=5,   gen_n=[2, 3],          holes=[0.5],           per_cell=2,  norvig=False),
    "quick": dict(time_limit=60,  gen_n=[4, 5, 6, 7],    holes=[0.4, 0.5, 0.6], per_cell=3,  norvig=True),
    "full":  dict(time_limit=600, gen_n=[4, 5, 6, 7, 8], holes=[0.4, 0.5, 0.6], per_cell=10, norvig=True),
}
NORVIG = {"9-top95": "https://norvig.com/top95.txt", "9-hardest": "https://norvig.com/hardest.txt"}

# =============================================================================
# 1. Instances
# =============================================================================
def write_instance(path, n, clues):
    N = n * n
    with open(path, "w") as f:
        f.write(f"{n}\n" + " ".join(str(clues.get((r, c), 0)) for r in range(N) for c in range(N)) + "\n")

def read_instance(path):
    with open(path) as f:
        n = int(f.readline()); vals = [int(t) for t in f.read().split()]
    N = n * n
    return n, {(i // N, i % N): v for i, v in enumerate(vals) if v}

def prepare_instances(prof, seed=2026):
    sets = {}
    if prof["norvig"]:
        for name, url in NORVIG.items():
            d = os.path.join(INST, name); os.makedirs(d, exist_ok=True)
            raw = os.path.join(d, os.path.basename(url))
            if not os.path.exists(raw):
                try:
                    import urllib.request
                    urllib.request.urlretrieve(url, raw)
                    print(f"  đã tải {url}")
                except Exception as e:
                    print(f"  ! không tải được {url} ({e}). Hãy tải tay và lưu thành {raw}")
                    continue
            files = []
            for i, line in enumerate(open(raw, encoding="utf-8", errors="ignore")):
                s = "".join(ch for ch in line if ch in "0123456789.")
                if len(s) != 81: continue
                p = os.path.join(d, f"{name}_{len(files)+1:03d}.txt")
                if not os.path.exists(p):
                    write_instance(p, 3, {(k // 9, k % 9): int(ch) for k, ch in enumerate(s) if ch not in ".0"})
                files.append(p)
            if files: sets[name] = files
    for n in prof["gen_n"]:
        N = n * n; name = f"Gen-{N}"; d = os.path.join(INST, name); os.makedirs(d, exist_ok=True)
        files = []
        for h in prof["holes"]:
            for k in range(prof["per_cell"]):
                p = os.path.join(d, f"gen{N}_h{int(h*100)}_{k+1:02d}.txt")
                if not os.path.exists(p):
                    rng = random.Random(f"{seed}-{N}-{h}-{k}")
                    clues, _ = S.make_puzzle(n, h, rng)
                    write_instance(p, n, clues)
                files.append(p)
        sets[name] = files
    return sets

# =============================================================================
# 2. Worker: solve ONE instance with ONE method, print a JSON line
# =============================================================================
class CallSink:
    def __init__(self, fn): self.fn, self.n = fn, 0
    def add(self, c): self.fn(c); self.n += 1

def run_external(exe, extra, n, amo, variant, clues, T, t0, info):
    """Ghi DIMACS (streaming) roi goi solver ngoai; exit 10 = SAT, 20 = UNSAT."""
    nv, ncl = S.formula_size(n, amo, variant, len(clues))
    fd, path = tempfile.mkstemp(suffix=".cnf"); os.close(fd)
    try:
        with open(path, "w") as f:
            f.write(f"p cnf {nv} {ncl}\n")
            sk = CallSink(lambda c: f.write(" ".join(map(str, c)) + " 0\n"))
            S.encode(n, amo, variant, clues, sink=sk)
        assert sk.n == ncl, "số mệnh đề khác công thức"
        info.update(vars=nv, clauses=ncl); t1 = time.perf_counter()
        left = max(1.0, T - (t1 - t0))
        p = subprocess.run([exe] + extra + [path], capture_output=True, text=True, timeout=left)
        if p.returncode == 10:
            true = [int(t) for line in p.stdout.splitlines() if line.startswith("v ")
                    for t in line[2:].split() if int(t) > 0]
        elif p.returncode == 20: true = None
        else: raise RuntimeError(f"{os.path.basename(exe)} exit {p.returncode}: {(p.stderr or p.stdout)[-200:]}")
        return true, t1
    finally:
        os.remove(path)

def solve_sat(solver, amo, variant, n, clues, T, cms_path=None):
    t0 = time.perf_counter(); info = {}
    if solver == "dpll":
        sink, nv = S.encode(n, amo, variant, clues)
        info.update(vars=nv, clauses=sink.n); t1 = time.perf_counter()
        N = n * n
        alo = [c for c in sink.clauses if len(c) == N and all(l > 0 for l in c)]
        m = S.dpll_solve(sink.clauses, nv, branch_clauses=alo)
        true = None if m is None else [v for v in range(1, nv + 1) if m[v] > 0]
    elif solver == "cms":
        exe = cms_path or shutil.which("cryptominisat5")
        try:
            from pycryptosat import Solver
        except ImportError:
            Solver = None
        if Solver is not None and not cms_path:
            s = Solver(threads=1)
            sk = CallSink(lambda c: s.add_clause(c)); _, nv = S.encode(n, amo, variant, clues, sink=sk)
            info.update(vars=nv, clauses=sk.n); t1 = time.perf_counter()
            ok, sol = s.solve()
            true = [i for i, v in enumerate(sol) if v is True] if ok else None
        elif exe:
            true, t1 = run_external(exe, ["--verb", "0", "--threads", "1"], n, amo, variant, clues, T, t0, info)
        else:
            raise RuntimeError("không có pycryptosat và không tìm thấy cryptominisat5 (cài một trong hai hoặc thêm --cms ĐƯỜNG_DẪN)")
    else:  # PySAT
        from pysat.solvers import Solver
        s = Solver(name=solver)
        sk = CallSink(lambda c: s.add_clause(c)); _, nv = S.encode(n, amo, variant, clues, sink=sk)
        info.update(vars=nv, clauses=sk.n); t1 = time.perf_counter()
        ok = s.solve()
        true = [l for l in s.get_model() if l > 0] if ok else None
        s.delete()
    t2 = time.perf_counter()
    grid = None if true is None else S.decode(n, true)
    return grid, t1 - t0, t2 - t1, info

def worker(a):
    n, clues = read_instance(a.instance)
    out = {"status": "ERR", "t_build": 0, "t_solve": 0, "t_total": 0}
    try:
        _, solver, amo, variant = a.method.split(":")
        grid, tb, ts, info = solve_sat(solver, amo, variant, n, clues, a.time_limit, a.cms)
        out.update(info, t_build=tb, t_solve=ts, t_total=tb + ts)
        if grid is None: out["status"] = "UNSAT"
        else: out["status"] = "SAT" if S.is_valid_solution(n, grid, clues) else "WRONG"
        if out["t_total"] > a.time_limit: out["status"] = "TO"
    except subprocess.TimeoutExpired:
        out.update(status="TO", t_total=a.time_limit)
    except MemoryError:
        out.update(status="MO", msg="hết bộ nhớ")
    except Exception as e:
        out.update(status="ERR", msg=f"{type(e).__name__}: {e}"[:300])
    print(json.dumps(out))

# =============================================================================
# 3. Availability check
# =============================================================================
TINY = os.path.join(INST, "_tiny.txt")

def available_solvers(paths, verbose=True):
    os.makedirs(INST, exist_ok=True)
    if not os.path.exists(TINY):
        write_instance(TINY, 2, {(0, 0): 1, (1, 2): 1})
    ok = []
    for sol in SAT_SOLVERS:
        r = run_one(f"sat:{sol}:seq:minimal", TINY, 30, paths)
        if r["status"] == "SAT": ok.append(sol)
        if verbose:
            print(f"  {'OK ' if r['status'] == 'SAT' else '-- '} {SAT_LABEL[sol]:16s} {'' if r['status'] == 'SAT' else r.get('msg', r['status'])[:100]}")
    return ok

# =============================================================================
# 4. Running
# =============================================================================
FIELDS = ["set", "instance", "method", "time_limit", "status", "t_build", "t_solve", "t_total", "vars", "clauses", "msg"]
_lock = threading.Lock()

def load_runs():
    if not os.path.exists(RUNS): return []
    with open(RUNS, newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        for k in ("t_build", "t_solve", "t_total", "time_limit"): r[k] = float(r[k] or 0)
    return rows

def append_run(row):
    with _lock:
        new = not os.path.exists(RUNS)
        os.makedirs(os.path.dirname(RUNS), exist_ok=True)
        with open(RUNS, "a", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=FIELDS)
            if new: w.writeheader()
            w.writerow({k: row.get(k, "") for k in FIELDS})

def run_one(method, inst, T, paths):
    cmd = [sys.executable, os.path.abspath(__file__), "worker", "--method", method,
           "--instance", inst, "--time-limit", str(T)]
    for k in ("cms",):
        if paths.get(k): cmd += [f"--{k}", paths[k]]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=T + 10)
        line = [l for l in p.stdout.splitlines() if l.startswith("{")]
        if line: return json.loads(line[-1])
        err = (p.stderr or "").strip().splitlines()
        st = "MO" if any("MemoryError" in l for l in err) else "ERR"
        return {"status": st, "t_total": 0, "msg": (err[-1] if err else f"exit {p.returncode}")[:300]}
    except subprocess.TimeoutExpired:
        return {"status": "TO", "t_total": T, "t_build": 0, "t_solve": T}

def run_batch(jobs, T, njobs, paths, done):
    todo = [(s, i, m) for (s, i, m) in jobs if (os.path.relpath(i, ROOT), m, float(T)) not in done]
    print(f"  {len(jobs)} lần chạy, {len(jobs)-len(todo)} đã có kết quả, còn {len(todo)}")
    cnt = [0]
    def go(job):
        s, i, m = job
        r = run_one(m, i, T, paths)
        r.update(set=s, instance=os.path.relpath(i, ROOT), method=m, time_limit=T)
        append_run(r)
        done.add((r["instance"], m, float(T)))
        with _lock:
            cnt[0] += 1
            print(f"  [{cnt[0]}/{len(todo)}] {s:10s} {os.path.basename(i):22s} {m:32s} {r['status']:5s} {r.get('t_total',0):8.2f}s")
    with ThreadPoolExecutor(max_workers=njobs) as ex:
        list(ex.map(go, todo))

def stats(rows, method, set_, T):
    rs = [r for r in rows if r["method"] == method and r["set"] == set_ and r["time_limit"] == T]
    if not rs: return None
    solved = [r for r in rs if r["status"] in ("SAT", "UNSAT")]
    par2 = sum(r["t_total"] if r["status"] in ("SAT", "UNSAT") else 2 * T for r in rs) / len(rs)
    return {"solved": len(solved), "total": len(rs), "par2": par2,
            "wrong": sum(r["status"] == "WRONG" for r in rs),
            "build": sum(r["t_build"] for r in solved), "solve": sum(r["t_solve"] for r in solved)}

def better(a, b):
    """True neu a tot hon b (giai duoc nhieu de hon, roi PAR-2 nho hon)."""
    if b is None: return a is not None
    if a is None: return False
    return (a["solved"], -a["par2"]) > (b["solved"], -b["par2"])

def total(rows, method, sets, T):
    agg = {"solved": 0, "total": 0, "par2": 0.0}
    for s in sets:
        st = stats(rows, method, s, T)
        if st: agg["solved"] += st["solved"]; agg["total"] += st["total"]; agg["par2"] += st["par2"]
    return agg

def key_total(rows, method, sets, T):
    t = total(rows, method, sets, T)
    return (t["solved"], -t["par2"]) if t["total"] else (-1, 0)

def cmd_run(a):
    prof = PROFILES[a.profile]; T = float(a.time_limit or prof["time_limit"])
    paths = {"cms": a.cms}
    print("1) Chuẩn bị bộ đề ...")
    sets = prepare_instances(prof)
    for k, v in sets.items(): print(f"  {k}: {len(v)} đề")
    print("2) Kiểm tra solver ...")
    sat_ok = available_solvers(paths)
    if a.profile == "smoke": sat_ok = sat_ok or ["dpll"]
    if not sat_ok: sys.exit("Không có SAT solver nào chạy được. Hãy cài python-sat (xem HUONG_DAN.md).")
    done = {(r["instance"], r["method"], r["time_limit"]) for r in load_runs()}
    fixed = sat_ok[0]
    setsA = [s for s in sets if s != "9-hardest"]
    print(f"3) Thí nghiệm A: 5 AMO x 2 biến thể với {SAT_LABEL[fixed]} trên {setsA}")
    jobs = [(s, i, f"sat:{fixed}:{amo}:{v}") for s in setsA for amo in AMOS for v in VARIANTS for i in sets[s]]
    run_batch(jobs, T, a.jobs, paths, done)
    rows = load_runs()
    best_cfg = max(((amo, v) for amo in AMOS for v in VARIANTS),
                   key=lambda c: key_total(rows, f"sat:{fixed}:{c[0]}:{c[1]}", setsA, T))
    print(f"   -> cấu hình tốt nhất: {best_cfg}")
    print(f"4) Thí nghiệm B: các SAT solver {sat_ok} với {best_cfg} và với pairwise + minimal")
    cfgs = [best_cfg] + ([("pairwise", "minimal")] if tuple(best_cfg) != ("pairwise", "minimal") else [])
    jobs = [(s, i, f"sat:{sol}:{c[0]}:{c[1]}") for c in cfgs for sol in sat_ok for s in sets for i in sets[s]]
    run_batch(jobs, T, a.jobs, paths, done)
    rows = load_runs()
    best_sat = max(sat_ok, key=lambda sol: key_total(rows, f"sat:{sol}:{best_cfg[0]}:{best_cfg[1]}", list(sets), T))
    print(f"   -> SAT solver tốt nhất: {best_sat}")
    meta = {"profile": a.profile, "time_limit": T, "sets": {k: len(v) for k, v in sets.items()},
            "fixed": fixed, "best_cfg": best_cfg, "best_sat": best_sat, "sat_ok": sat_ok,
            "gen_n": prof["gen_n"], "holes": prof["holes"], "per_cell": prof["per_cell"], "jobs": a.jobs,
            "cms": a.cms}
    json.dump(meta, open(os.path.join(REPORT, "results", "meta.json"), "w"), indent=1, ensure_ascii=False)
    print("5) Tạo bảng, hình và đoạn văn cho báo cáo ...")
    cmd_report(a)

# =============================================================================
# 5. Report generation
# =============================================================================
def tex_escape(s):
    s = str(s)
    for k, v in (("\\", r"\textbackslash{}"), ("&", r"\&"), ("%", r"\%"), ("$", r"\$"), ("#", r"\#"),
                 ("_", r"\_"), ("{", r"\{"), ("}", r"\}"), ("~", r"\textasciitilde{}"), ("^", r"\^{}")):
        s = s.replace(k, v)
    return s

def vn(x, d=2):
    """So kieu Viet Nam: 1.234,56"""
    s = f"{x:,.{d}f}" if d else f"{int(round(x)):,}"
    return s.replace(",", "X").replace(".", ",").replace("X", ".")

def cell(st, best=False):
    if st is None: return "--"
    t = f"{st['solved']}/{st['total']} ({vn(st['par2'], 2 if st['par2'] < 100 else 1)})"
    if st["wrong"]: t += r"$^{!}$"
    return r"\textbf{" + t + "}" if best else t

def machine_info():
    cpu = platform.processor() or ""
    try:
        if sys.platform.startswith("linux"):
            for line in open("/proc/cpuinfo"):
                if line.startswith("model name"): cpu = line.split(":", 1)[1].strip(); break
        elif sys.platform == "darwin":
            cpu = subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True, text=True).stdout.strip() or cpu
    except Exception: pass
    ram = None
    try:
        import psutil; ram = psutil.virtual_memory().total
    except Exception:
        try:
            for line in open("/proc/meminfo"):
                if line.startswith("MemTotal"): ram = int(line.split()[1]) * 1024; break
        except Exception: pass
    return {"cpu": cpu or "không xác định", "cores": os.cpu_count(),
            "ram": f"{ram/2**30:.0f} GB" if ram else "không xác định",
            "os": f"{platform.system()} {platform.release()}", "python": platform.python_version()}

def solver_versions(meta):
    v = {}
    def tryv(key, fn):
        try: v[key] = str(fn()).strip().splitlines()[0]
        except Exception: v[key] = None
    tryv("pysat", lambda: __import__("pysat").__version__)
    v["cadical195"] = "1.9.5" + (f" (PySAT {v['pysat']})" if v.get("pysat") else "")
    v["glucose4"] = "4.1" + (f" (PySAT {v['pysat']})" if v.get("pysat") else "")
    import importlib.util
    if meta.get("cms") or importlib.util.find_spec("pycryptosat") is None:
        tryv("cms", lambda: subprocess.run([meta.get("cms") or shutil.which("cryptominisat5"), "--version"], capture_output=True, text=True).stdout)
    else:
        tryv("cms", lambda: "pycryptosat " + __import__("pycryptosat").__version__)
    return v

def cmd_report(a):
    rows = load_runs()
    mp = os.path.join(REPORT, "results", "meta.json")
    if not rows or not os.path.exists(mp):
        sys.exit("Chưa có kết quả. Hãy chạy: python run_experiments.py run --profile quick")
    meta = json.load(open(mp, encoding="utf-8")); T = float(meta["time_limit"])
    sets = list(meta["sets"]); fixed = meta["fixed"]; bc = tuple(meta["best_cfg"]); bs = meta["best_sat"]
    setsA = [s for s in sets if s != "9-hardest"]
    tdir = os.path.join(REPORT, "tables"); os.makedirs(tdir, exist_ok=True)
    W = lambda name, txt: open(os.path.join(tdir, name), "w", encoding="utf-8").write(txt)
    lab = lambda k: S.AMO_LABEL[k]
    M_ = lambda sol, c=bc: f"sat:{sol}:{c[0]}:{c[1]}"

    # ---- Bang A: AMO x bien the voi solver co dinh
    L = [r"\begin{tabular}{ll" + "c" * len(AMOS) + "}", r"\toprule",
         "Bộ & Biến thể & " + " & ".join(lab(k) for k in AMOS) + r" \\", r"\midrule"]
    for s in setsA:
        for j, v in enumerate(VARIANTS):
            st = {k: stats(rows, f"sat:{fixed}:{k}:{v}", s, T) for k in AMOS}
            b = None
            for k in AMOS:
                if better(st[k], st[b] if b else None): b = k
            first = (r"\multirow{2}{*}{" + s + "}") if j == 0 else ""
            L.append(f"{first} & {v} & " + " & ".join(cell(st[k], k == b) for k in AMOS) + r" \\")
    L += [r"\bottomrule", r"\end{tabular}"]; W("res_amo.tex", "\n".join(L) + "\n")

    # ---- Bang B: cac SAT solver, voi cau hinh tot nhat va voi pairwise+minimal
    solvers = [x for x in SAT_SOLVERS + ["dpll"] if any(r["method"] == M_(x) for r in rows)]
    cfgs = [bc] + ([("pairwise", "minimal")] if bc != ("pairwise", "minimal") else [])
    L = [r"\begin{tabular}{ll" + "c" * len(sets) + "}", r"\toprule",
         "Cấu hình & Solver & " + " & ".join(sets) + r" \\", r"\midrule"]
    for ci, c in enumerate(cfgs):
        best = {}
        for s in sets:
            b = None
            for x in solvers:
                if better(stats(rows, M_(x, c), s, T), stats(rows, M_(b, c), s, T) if b else None): b = x
            best[s] = b
        for j, x in enumerate(solvers):
            first = (r"\multirow{" + str(len(solvers)) + r"}{*}{\shortstack[l]{" + lab(c[0]) + r"\\" + c[1] + "}}") if j == 0 else ""
            L.append(f"{first} & {SAT_LABEL[x]} & " + " & ".join(cell(stats(rows, M_(x, c), s, T), best[s] == x) for s in sets) + r" \\")
        if ci < len(cfgs) - 1: L.append(r"\midrule")
    L += [r"\bottomrule", r"\end{tabular}"]; W("res_solvers.tex", "\n".join(L) + "\n")

    # ---- Bang phien ban solver + bang du lieu
    ver = solver_versions(meta)
    def vcell(k): return tex_escape(ver.get(k) or "--") if k in meta["sat_ok"] else "không chạy"
    cms_how = r"\texttt{pycryptosat}" if (ver.get("cms") or "").startswith("pycryptosat") else r"file chạy \texttt{cryptominisat5}, đọc DIMACS"
    W("solvers.tex", "\n".join([
        r"\begin{tabular}{lll}", r"\toprule", r"Solver & Cách gọi & Phiên bản\\", r"\midrule",
        r"CaDiCaL~\citep{biere2020} & PySAT (\texttt{cadical195}) & " + vcell("cadical195") + r"\\",
        r"Glucose~\citep{audemard2009} & PySAT (\texttt{glucose4}) & " + vcell("glucose4") + r"\\",
        r"CryptoMiniSat~\citep{soos2009} & " + cms_how + " & " + vcell("cms") + r"\\",
        r"\bottomrule", r"\end{tabular}"]) + "\n")
    B = [r"\begin{tabular}{llcc}", r"\toprule", r"Bộ & Nguồn & $N$ & Số đề\\", r"\midrule"]
    for s, cnt in meta["sets"].items():
        if s.startswith("9-"): B.append(f"{s} & \\citet{{norvig}} & 9 & {cnt}" + r"\\")
        else: B.append(f"{s} & tự sinh, {meta['per_cell']} đề mỗi $h$ & {s.split('-')[1]} & {cnt}" + r"\\")
    B += [r"\bottomrule", r"\end{tabular}"]; W("bench.tex", "\n".join(B) + "\n")

    # ---- cactus: cac SAT solver voi cau hinh tot nhat
    try:
        import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
        plt.rcParams.update({"font.size": 8, "font.family": "serif"})
        fig, ax = plt.subplots(figsize=(5.2, 3.0))
        for x in solvers:
            ts = sorted(r["t_total"] for r in rows if r["method"] == M_(x) and r["time_limit"] == T and r["status"] in ("SAT", "UNSAT"))
            if ts: ax.plot(range(1, len(ts) + 1), ts, marker=".", ms=3, lw=1, label=SAT_LABEL[x])
        ax.set_yscale("log"); ax.set_xlabel("Số đề giải được"); ax.set_ylabel("Thời gian (giây)")
        ax.axhline(T, color="gray", ls="--", lw=0.8); ax.grid(alpha=.3); ax.legend(fontsize=7, frameon=False)
        plt.tight_layout(); plt.savefig(os.path.join(REPORT, "figures", "cactus.pdf")); plt.close()
    except Exception as e:
        print("  ! không vẽ được cactus:", e)

    # ---- doan van tu dong
    mi = machine_info()
    tot = lambda m, ss: total(rows, m, ss, T)
    cfgs_all = sorted(((amo, v) for amo in AMOS for v in VARIANTS),
                      key=lambda c: (-tot(f"sat:{fixed}:{c[0]}:{c[1]}", setsA)["solved"], tot(f"sat:{fixed}:{c[0]}:{c[1]}", setsA)["par2"]))
    cb, cw = cfgs_all[0], cfgs_all[-1]
    tb, tw = tot(f"sat:{fixed}:{cb[0]}:{cb[1]}", setsA), tot(f"sat:{fixed}:{cw[0]}:{cw[1]}", setsA)
    ext_b = sum(1 for s in setsA for k in AMOS if better(stats(rows, f"sat:{fixed}:{k}:extended", s, T), stats(rows, f"sat:{fixed}:{k}:minimal", s, T)))
    min_b = sum(1 for s in setsA for k in AMOS if better(stats(rows, f"sat:{fixed}:{k}:minimal", s, T), stats(rows, f"sat:{fixed}:{k}:extended", s, T)))
    gens = [s for s in setsA if s.startswith("Gen-")]
    big = gens[-1] if gens else setsA[-1]
    Nbig = 9 if big.startswith("9-") else int(big.split("-")[1]); nbig = int(round(Nbig ** 0.5))
    by_par = sorted(AMOS, key=lambda k: (lambda st: (-(st or {"solved": 0})["solved"], (st or {"par2": 1e18})["par2"]))(stats(rows, f"sat:{fixed}:{k}:minimal", big, T)))
    by_cls = sorted(AMOS, key=lambda k: S.formula_size(nbig, k, "minimal")[1])
    amo_txt = (f"Với {SAT_LABEL[fixed]}, cấu hình tốt nhất là {lab(cb[0])} + {cb[1]}: giải được {tb['solved']}/{tb['total']} đề, "
               f"tổng PAR-2 trên các bộ là {vn(tb['par2'])} giây. Cấu hình kém nhất là {lab(cw[0])} + {cw[1]} "
               f"({tw['solved']}/{tw['total']} đề, tổng PAR-2 {vn(tw['par2'])} giây). "
               f"Trong {len(setsA)*len(AMOS)} cặp (bộ dữ liệu, AMO), mã hóa extended tốt hơn minimal ở {ext_b} cặp, "
               f"minimal tốt hơn ở {min_b} cặp, các cặp còn lại như nhau. "
               f"Trên bộ {big}, thứ tự theo thời gian (tốt nhất trước) là {', '.join(lab(k) for k in by_par)}, "
               f"còn thứ tự theo số mệnh đề (ít nhất trước) là {', '.join(lab(k) for k in by_cls)}; "
               + ("hai thứ tự này trùng nhau." if by_par == by_cls else "hai thứ tự này không hoàn toàn trùng nhau, nghĩa là kích thước công thức chưa giải thích hết thời gian chạy."))
    rank = sorted(solvers, key=lambda x: (-tot(M_(x), sets)["solved"], tot(M_(x), sets)["par2"]))
    per_set = []
    for s in sets:
        b = None
        for x in solvers:
            if better(stats(rows, M_(x), s, T), stats(rows, M_(b), s, T) if b else None): b = x
        if b: per_set.append(f"{s}: {SAT_LABEL[b]}")
    solver_txt = (f"Với cấu hình {lab(bc[0])} + {bc[1]}, xếp theo số đề giải được rồi đến PAR-2, thứ tự các solver là "
                  + ", ".join(f"{SAT_LABEL[x]} ({tot(M_(x), sets)['solved']}/{tot(M_(x), sets)['total']})" for x in rank) + ". "
                  + "Solver tốt nhất trên từng bộ: " + "; ".join(per_set) + ". ")
    if len(cfgs) > 1:
        pw = ("pairwise", "minimal")
        gain = [x for x in solvers if better(tot(M_(x), sets) | {"wrong": 0}, tot(M_(x, pw), sets) | {"wrong": 0})]
        solver_txt += (f"So với pairwise + minimal, cấu hình {lab(bc[0])} + {bc[1]} tốt hơn với "
                       + (", ".join(SAT_LABEL[x] for x in gain) if gain else "không solver nào")
                       + f" ({len(gain)}/{len(solvers)} solver), tức là cấu hình tốt nhất tìm được với {SAT_LABEL[fixed]} "
                       + ("cũng có lợi cho các solver khác." if len(gain) == len(solvers) else "không nhất thiết tốt nhất cho mọi solver."))
    miss = [SAT_LABEL[x] for x in SAT_SOLVERS if x not in meta["sat_ok"]]
    if miss: solver_txt += f" Không chạy được trên máy thử nghiệm: {', '.join(miss)}."
    def share(m):
        st = [stats(rows, m, s, T) for s in sets]; bsum = sum(x["build"] for x in st if x); ssum = sum(x["solve"] for x in st if x)
        return 100 * bsum / (bsum + ssum) if bsum + ssum > 0 else 0
    def maxN(m):
        best = None
        for s in sets:
            st = stats(rows, m, s, T)
            if st and st["solved"] == st["total"]:
                N = 9 if s.startswith("9-") else int(s.split("-")[1]); best = max(best or 0, N)
        return best
    scale_txt = ("$N$ lớn nhất mà mỗi solver giải hết các đề trong giới hạn " + vn(T, 0) + " giây (cấu hình " + f"{lab(bc[0])} + {bc[1]}): "
                 + "; ".join(f"{SAT_LABEL[x]}: " + (f"${maxN(M_(x))}\\times{maxN(M_(x))}$" if maxN(M_(x)) else "không có") for x in solvers) + ". "
                 + f"Với {SAT_LABEL[bs]}, thời gian sinh công thức chiếm {vn(share(M_(bs)), 0)}\\% tổng thời gian của các đề giải được. ")
    bad = [r for r in rows if r["status"] in ("MO", "ERR", "WRONG") and r["time_limit"] == T]
    if bad: scale_txt += f"Có {len(bad)} lần chạy lỗi hoặc hết bộ nhớ (xem cột msg trong \\texttt{{results/runs.csv}}). "
    if any(r["status"] == "WRONG" for r in bad):
        scale_txt += r"\textcolor{red}{Có lời giải sai (đánh dấu $^{!}$ trong bảng), cần kiểm tra lại code.} "
    n_all = sum(meta["sets"].values()); bt = tot(M_(bs), sets); msat = maxN(M_(bs))
    abstract_txt = (f"Trên {n_all} đề thử nghiệm với giới hạn {vn(T,0)} giây, cấu hình mã hóa tốt nhất là AMO {lab(bc[0])} với mã hóa {bc[1]}, "
                    f"và {SAT_LABEL[bs]} là solver tốt nhất, giải được {bt['solved']}/{bt['total']} đề.")
    concl_txt = abstract_txt + (f" Lưới lớn nhất mà {SAT_LABEL[bs]} giải hết các đề là ${msat}\\times{msat}$." if msat else "")
    maxgen = max([int(s.split("-")[1]) for s in sets if s.startswith("Gen-")] or [9])
    def M(name, val): return f"\\renewcommand{{\\{name}}}{{{val}}}\n"
    txt = ("% TU DONG SINH boi run_experiments.py -- hay doc lai va sua cho tu nhien.\n"
           + M("MachineCPU", tex_escape(mi["cpu"])) + M("MachineCores", mi["cores"]) + M("MachineRAM", tex_escape(mi["ram"]))
           + M("MachineOS", tex_escape(mi["os"])) + M("PythonVersion", mi["python"]) + M("TimeLimit", vn(T, 0))
           + M("RepeatText", "Mỗi đề chạy một lần với mỗi cấu hình" + (f", chạy song song {meta['jobs']} tiến trình" if meta["jobs"] > 1 else "") + ".")
           + M("FixedSolver", SAT_LABEL[fixed]) + M("BestConfig", f"{lab(bc[0])} + {bc[1]}") + M("BestSolver", SAT_LABEL[bs])
           + M("MaxGenN", maxgen) + M("GenPerCell", meta["per_cell"])
           + M("GenSizes", ", ".join(str(n*n) for n in meta["gen_n"])) + M("HoleRatios", ", ".join(str(h) for h in meta["holes"]))
           + M("AutoAbstract", abstract_txt) + M("AutoAmo", amo_txt) + M("AutoSolvers", solver_txt)
           + M("AutoScale", scale_txt) + M("AutoConclusion", concl_txt))
    open(os.path.join(REPORT, "results", "auto_text.tex"), "w", encoding="utf-8").write(txt)
    print("  đã ghi tables/res_*.tex, tables/solvers.tex, tables/bench.tex, figures/cactus.pdf, results/auto_text.tex")

# =============================================================================
# 6. Placeholders (reset) and author info
# =============================================================================
PLACEHOLDER_TEXT = {
    "MachineCPU": r"\TODO{CPU}", "MachineCores": r"\TODO{số luồng}", "MachineRAM": r"\TODO{RAM}",
    "MachineOS": r"\TODO{hệ điều hành}", "PythonVersion": r"\TODO{phiên bản}", "TimeLimit": r"\TODO{600}",
    "RepeatText": r"\TODO{Ghi số lần chạy lặp.}", "FixedSolver": r"\TODO{CaDiCaL}",
    "BestConfig": r"\TODO{cấu hình tốt nhất}", "BestSolver": r"\TODO{solver tốt nhất}", "MaxGenN": r"\TODO{64}",
    "GenPerCell": "10", "GenSizes": "16, 25, 36, 49, 64", "HoleRatios": "0.4, 0.5, 0.6",
    "AutoAbstract": r"\TODO{Viết 1--2 câu về kết quả thực nghiệm chính.}",
    "AutoAmo": r"\TODO{Nhận xét: cấu hình nào giải được nhiều đề nhất; extended có giúp ích không; thứ tự theo số mệnh đề có trùng với thứ tự theo thời gian không.}",
    "AutoSolvers": r"\TODO{Nhận xét thứ hạng các SAT solver; cấu hình tốt nhất có tốt cho mọi solver không.}",
    "AutoScale": r"\TODO{Ghi $N$ lớn nhất mỗi solver giải hết; tỉ lệ thời gian sinh công thức; các lần chạy lỗi.}",
    "AutoConclusion": r"\TODO{Tóm tắt kết quả thực nghiệm.}",
}

def cmd_reset(a=None):
    tdir = os.path.join(REPORT, "tables"); os.makedirs(tdir, exist_ok=True)
    os.makedirs(os.path.join(REPORT, "results"), exist_ok=True)
    txt = "% CHO TRONG -- se bi ghi de khi chay run_experiments.py run\n" + "".join(
        f"\\renewcommand{{\\{k}}}{{{v}}}\n" for k, v in PLACEHOLDER_TEXT.items())
    open(os.path.join(REPORT, "results", "auto_text.tex"), "w", encoding="utf-8").write(txt)
    t = r"\textcolor{red}{\textbf{--}}"
    setsA = ["9-top95", "Gen-25", "Gen-49", "Gen-64"]; setsB = ["9-top95", "9-hardest", "Gen-25", "Gen-49", "Gen-64"]
    L = [r"\begin{tabular}{ll" + "c" * 5 + "}", r"\toprule", "Bộ & Biến thể & " + " & ".join(S.AMO_LABEL[k] for k in AMOS) + r" \\", r"\midrule"]
    for s in setsA:
        for j, v in enumerate(VARIANTS):
            L.append(((r"\multirow{2}{*}{" + s + "}") if j == 0 else "") + f" & {v} & " + " & ".join([t] * 5) + r" \\")
    L += [r"\bottomrule", r"\end{tabular}"]
    open(os.path.join(tdir, "res_amo.tex"), "w", encoding="utf-8").write("\n".join(L) + "\n")
    L = [r"\begin{tabular}{ll" + "c" * len(setsB) + "}", r"\toprule", "Cấu hình & Solver & " + " & ".join(setsB) + r" \\", r"\midrule"]
    for ci, cname in enumerate([r"\TODO{tốt nhất}", r"\shortstack[l]{Pairwise\\minimal}"]):
        for j, x in enumerate(SAT_SOLVERS):
            L.append(((r"\multirow{" + str(len(SAT_SOLVERS)) + r"}{*}{" + cname + "}") if j == 0 else "") + f" & {SAT_LABEL[x]} & " + " & ".join([t] * len(setsB)) + r" \\")
        if ci == 0: L.append(r"\midrule")
    L += [r"\bottomrule", r"\end{tabular}"]
    open(os.path.join(tdir, "res_solvers.tex"), "w", encoding="utf-8").write("\n".join(L) + "\n")
    td = r"\TODO{\,}"
    open(os.path.join(tdir, "solvers.tex"), "w", encoding="utf-8").write("\n".join([
        r"\begin{tabular}{lll}", r"\toprule", r"Solver & Cách gọi & Phiên bản\\", r"\midrule",
        r"CaDiCaL~\citep{biere2020} & PySAT (\texttt{cadical195}) & " + td + r"\\",
        r"Glucose~\citep{audemard2009} & PySAT (\texttt{glucose4}) & " + td + r"\\",
        r"CryptoMiniSat~\citep{soos2009} & \texttt{pycryptosat} hoặc file chạy \texttt{cryptominisat5} & " + td + r"\\",
        r"\bottomrule", r"\end{tabular}"]) + "\n")
    open(os.path.join(tdir, "bench.tex"), "w", encoding="utf-8").write("\n".join([
        r"\begin{tabular}{llcc}", r"\toprule", r"Bộ & Nguồn & $N$ & Số đề\\", r"\midrule",
        r"9-top95 & \citet{norvig} & 9 & 95\\", r"9-hardest & \citet{norvig} & 9 & 11\\",
        r"Gen-$N$ & tự sinh, 10 đề mỗi $(N,h)$ & 16, 25, 36, 49, 64 & 150\\",
        r"\bottomrule", r"\end{tabular}"]) + "\n")
    cp = os.path.join(REPORT, "figures", "cactus.pdf")
    if os.path.exists(cp): os.remove(cp)
    for old in ("res_base.tex",):
        if os.path.exists(os.path.join(tdir, old)): os.remove(os.path.join(tdir, old))
    print("Đã đưa báo cáo về trạng thái chữ đỏ (results/runs.csv vẫn được giữ).")

def cmd_info(a):
    p = os.path.join(REPORT, "results", "author.tex")
    old = {}
    if os.path.exists(p):
        for line in open(p, encoding="utf-8"):
            m = re.match(r"\\renewcommand\{\\(\w+)\}\{(.*)\}$", line.strip())
            if m: old[m.group(1)] = m.group(2)
    new = dict(old)
    if a.name: new["AuthorName"] = tex_escape(a.name)
    if a.email: new["AuthorEmail"] = tex_escape(a.email)
    if a.github: new["GithubURL"] = r"\url{" + a.github + "}"
    open(p, "w", encoding="utf-8").write("".join(f"\\renewcommand{{\\{k}}}{{{v}}}\n" for k, v in new.items()))
    print("Đã ghi", p)

# =============================================================================
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp = ap.add_subparsers(dest="cmd", required=True)
    def paths(p): p.add_argument("--cms", help="đường dẫn file chạy cryptominisat5 (nếu không dùng pycryptosat)")
    p = sp.add_parser("check"); paths(p)
    p = sp.add_parser("run"); p.add_argument("--profile", default="quick", choices=list(PROFILES))
    p.add_argument("--time-limit", type=float); p.add_argument("--jobs", type=int, default=1); paths(p)
    sp.add_parser("report"); sp.add_parser("reset")
    p = sp.add_parser("info"); p.add_argument("--name"); p.add_argument("--email"); p.add_argument("--github")
    p = sp.add_parser("worker"); p.add_argument("--method"); p.add_argument("--instance")
    p.add_argument("--time-limit", type=float); paths(p)
    a = ap.parse_args()
    if a.cmd == "worker": return worker(a)
    if a.cmd == "check":
        print("Kiểm tra SAT solver (OK = chạy được):"); available_solvers({"cms": a.cms}); return
    if a.cmd == "run": return cmd_run(a)
    if a.cmd == "report": return cmd_report(a)
    if a.cmd == "reset": return cmd_reset(a)
    if a.cmd == "info": return cmd_info(a)

if __name__ == "__main__":
    main()
