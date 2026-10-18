# Báo cáo BTL 1 — Sudoku solver dùng SAT (3 SAT solver: CaDiCaL, Glucose, CryptoMiniSat)

## Cấu trúc
- `report/sudoku_sat_report.tex` — báo cáo theo template Elsevier `cas-sc`.
- `report/tables/`, `report/figures/`, `report/results/` — bảng, hình, số liệu sinh tự động.
- `code/sudoku_sat.py` — encoder Sudoku (minimal/extended), 5 cách mã hóa AMO, công thức kích thước, bộ kiểm thử, bộ sinh đề, ghi DIMACS, wrapper PySAT.
- `code/make_example_figure.py` — sinh Hình 2.
- `code/run_experiments.py` — chạy toàn bộ thực nghiệm và tự điền báo cáo.

## Biên dịch trên Overleaf
1. Tạo project từ template "Elsevier CAS".
2. Tải toàn bộ thư mục `report/` lên, chọn `sudoku_sat_report.tex` làm file chính.
3. Menu → Settings → Compiler: chọn **XeLaTeX**.
4. Recompile (Overleaf tự chạy BibTeX).

