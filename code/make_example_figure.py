#!/usr/bin/env python3
"""Solve the 9x9 example puzzle with the SAT encoding and write TikZ for the report."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import sudoku_sat as S

def grid_tikz(grid, clues, colour_new):
    L = ["\\begin{tikzpicture}[x=0.52cm,y=0.52cm]"]
    for r in range(9):
        for c in range(9):
            d = grid[r][c]
            if d == 0: continue
            if (r, c) in clues: L.append(f"\\node at ({c+.5},{8.5-r}) {{\\small\\textbf{{{d}}}}};")
            else: L.append(f"\\node[{colour_new}] at ({c+.5},{8.5-r}) {{\\small {d}}};")
    for i in range(10):
        w = "1.1pt" if i % 3 == 0 else "0.3pt"
        L.append(f"\\draw[line width={w}] (0,{i}) -- (9,{i}); \\draw[line width={w}] ({i},0) -- ({i},9);")
    L.append("\\end{tikzpicture}")
    return "\n".join(L)

clues = S.parse_puzzle(S.WIKI, 9)
sol = S.solve_dpll(3, "seq", "minimal", clues)
assert S.is_valid_solution(3, sol, clues)
puzzle = [[clues.get((r, c), 0) for c in range(9)] for r in range(9)]
out = os.path.join(os.path.dirname(__file__), "..", "report", "figures", "sudoku_example.tex")
open(out, "w").write(
    "\\begin{minipage}[t]{0.47\\linewidth}\\centering\n" + grid_tikz(puzzle, clues, "blue!70!black") +
    "\n\\\\[2pt] (a) đề bài (%d ô cho trước)\n\\end{minipage}\\hfill\n" % len(clues) +
    "\\begin{minipage}[t]{0.47\\linewidth}\\centering\n" + grid_tikz(sol, clues, "blue!70!black") +
    "\n\\\\[2pt] (b) lời giải đọc từ mô hình SAT\n\\end{minipage}\n")
print("clues:", len(clues), "-> wrote", out)
