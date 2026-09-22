"""Plot measured E_n automata separately from the proved mathematical lower bound."""

import csv
import html
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments/dfa_growth"


def main():
    font = Path("C:/Windows/Fonts/msyh.ttc")
    if font.exists():
        font_manager.fontManager.addfont(str(font))
        plt.rcParams["font.family"] = [font_manager.FontProperties(fname=str(font)).get_name(), "DejaVu Sans"]
    plt.rcParams["axes.unicode_minus"] = False
    measured = json.loads((OUT / "model_measurements.json").read_text(encoding="utf-8"))
    cli = {r["n"]: r for r in json.loads((OUT / "cli_measurements.json").read_text(encoding="utf-8"))}
    fig, axes = plt.subplots(1, 3, figsize=(18, 6.2))
    ax = axes[0]
    widths = [r["alphabetic_width"] for r in measured]
    counts = [r["minimal_projected_states"] for r in measured]
    ax.plot(widths, counts, "o-", label="独立模型：最小投影 DFA", color="#146f95")
    done = [r for r in cli.values() if r["status"] == "complete"]
    ax.plot([r["alphabetic_width"] for r in done], [r["structural_states"] for r in done],
            "s--", label="现有 CLI：结构状态", color="#d48422")
    for x, y in zip(widths, counts):
        ax.annotate(f"{y:,}", (x, y), xytext=(0, 9), textcoords="offset points", ha="center", fontsize=10)
    ax.set_yscale("log")
    ax.margins(y=.18)
    ax.set_xlabel("展开后的字母出现次数 N")
    ax.set_ylabel("实际完整 DFA 的状态数（对数刻度）")
    ax.set_title("① 已完成计算：n = 1,…,5")
    ax.legend(fontsize=9, loc="upper left")
    ax.text(.02, .02, "超时不作为状态数；两种 DFA 分开计量", transform=ax.transAxes, fontsize=9)
    ns = list(range(2, 41))
    widths_theory = [n*n + 8*n + 7 for n in ns]
    exponents = [math.comb(n, n // 2) for n in ns]
    ax = axes[1]
    ax.plot(widths_theory, exponents, color="#7757a7")
    ax.set_yscale("log", base=2)
    ax.set_xlabel("展开后的字母出现次数 N = n² + 8n + 7")
    ax.set_ylabel("log₂(状态下界) = 中央二项式系数（对数刻度）")
    ax.set_title("② 数学下界：不是大实例运行结果")
    ax.text(.03, .93, "状态数 ≥ 2^C(n,⌊n/2⌋)", transform=ax.transAxes, va="top", fontsize=11)
    ax = axes[2]
    ax.plot(ns, [math.log2(x) for x in exponents], label="log₂ log₂(状态下界)", color="#7757a7")
    ax.plot(ns, [n-math.log2(n+1) for n in ns], "--", label="n − log₂(n+1)", color="#29916c")
    ax.set_xlabel("前瞻条件数量 n（不是字面表达式长度）")
    ax.set_ylabel("取两次 log₂ 后的状态下界")
    ax.set_title("③ 两层指数的依据")
    ax.legend(fontsize=9)
    for ax in axes:
        ax.grid(True, which="major", alpha=.22)
    fig.suptitle("REwPLA 表达式族的 DFA 增长：实际计算与数学下界", fontsize=17)
    fig.text(.5, .015,
             "实验未新增 Rocq 下界证明。按展开宽度 N，下界为 2^(2^Ω(√N))；少量数据点本身不能证明渐近增长率。",
             ha="center", fontsize=10)
    fig.tight_layout(rect=(0, .065, 1, .93))
    for ext in ("png", "svg", "pdf"):
        fig.savefig(OUT / f"dfa_growth.{ext}", dpi=180)
    plt.close(fig)
    fields = ["n", "alphabetic_width", "expression_characters", "independent_reachable_states",
              "minimal_projected_states", "cli_status", "cli_structural_states", "theoretical_lower_bound"]
    with (OUT / "growth.csv").open("w", newline="", encoding="utf-8-sig") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for r in measured:
            row = {key: r[key] for key in fields if key in r}
            c = cli.get(r["n"], {})
            row.update(cli_status=c.get("status", "not_run"), cli_structural_states=c.get("structural_states", ""))
            writer.writerow(row)
    with (OUT / "theoretical_lower_bounds.csv").open("w", newline="", encoding="utf-8-sig") as stream:
        writer = csv.writer(stream)
        writer.writerow(["n", "alphabetic_width", "log2_lower_bound", "log2_log2_lower_bound"])
        writer.writerows((n, w, e, math.log2(e)) for n, w, e in zip(ns, widths_theory, exponents))
    rows = []
    for r in measured:
        c = cli.get(r["n"], {})
        cli_cell = str(c.get("structural_states", c.get("status", "未运行")))
        rows.append(f'<tr><td>{r["n"]}</td><td>{r["alphabetic_width"]}</td><td>{r["expression_characters"]}</td>'
                    f'<td>{r["minimal_projected_states"]:,}</td><td>{html.escape(cli_cell)}</td></tr>')
    expressions = "".join(f'<details><summary>n={r["n"]}，字母表 {r["alphabet"]}</summary>'
                           f'<pre>{html.escape(r["expression"])}</pre></details>' for r in measured)
    (OUT / "dfa_growth.html").write_text('''<!doctype html><html lang="zh-CN"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>REwPLA DFA 状态增长</title>
<style>body{font:16px/1.6 system-ui;max-width:1500px;margin:30px auto;padding:0 20px;color:#20313f}
img{width:100%}table{border-collapse:collapse}th,td{padding:8px 20px;border:1px solid #ccc}
pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#eee;padding:15px}details{margin:12px 0}</style>
<h1>REwPLA DFA 状态增长</h1><p>蓝色曲线是完整计算并最小化的投影 DFA；橙色曲线是现有 CLI 的结构状态。
紫色曲线是数学下界，不能当成实际生成的大 DFA。达到几千个状态本身不能证明双指数。</p>
<img src="dfa_growth.svg" alt="状态增长的三个图：实际计算、数学下界、两次对数">
<table><tr><th>n</th><th>字母出现次数 N</th><th>输入字符数</th><th>最小投影 DFA</th><th>CLI 结构状态 / 状态</th></tr>'''
        + "".join(rows) + '</table><h2>可展开查看的实际输入</h2>' + expressions
        + '<p>实验脚本和数学证明说明见 <a href="README.md">README.md</a>；<a href="growth.csv">下载测量数据 CSV</a>。</p></html>\n', encoding="utf-8")
    print(json.dumps({"plots": [str(OUT / f"dfa_growth.{ext}") for ext in ("png", "svg", "pdf", "html")],
                      "measured_minimal_states": counts}))


if __name__ == "__main__":
    main()
