#!/usr/bin/env python3
"""Generate dependency-free SVG figures from the evaluation CSV files."""

from __future__ import annotations

import argparse
import csv
import html
import math
from pathlib import Path


WIDTH = 860
HEIGHT = 520
LEFT = 88
RIGHT = 24
TOP = 54
BOTTOM = 72


def read_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as source:
        return list(csv.DictReader(source))


def svg_text(x: float, y: float, text: object, **attributes: object) -> str:
    attrs = " ".join(f'{key.replace("_", "-")}="{value}"' for key, value in attributes.items())
    return f'<text x="{x:.2f}" y="{y:.2f}" {attrs}>{html.escape(str(text))}</text>'


def polyline(points: list[tuple[float, float]], color: str, dash: str = "") -> str:
    coordinates = " ".join(f"{x:.2f},{y:.2f}" for x, y in points)
    dash_attribute = f' stroke-dasharray="{dash}"' if dash else ""
    return (
        f'<polyline points="{coordinates}" fill="none" stroke="{color}" '
        f'stroke-width="2.5"{dash_attribute}/>'
    )


def frame(title: str, x_label: str, y_label: str) -> list[str]:
    plot_right = WIDTH - RIGHT
    plot_bottom = HEIGHT - BOTTOM
    return [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{WIDTH}" height="{HEIGHT}" '
        f'viewBox="0 0 {WIDTH} {HEIGHT}">',
        '<rect width="100%" height="100%" fill="white"/>',
        svg_text(WIDTH / 2, 30, title, text_anchor="middle", font_family="sans-serif", font_size="20"),
        f'<line x1="{LEFT}" y1="{plot_bottom}" x2="{plot_right}" y2="{plot_bottom}" stroke="#333"/>',
        f'<line x1="{LEFT}" y1="{TOP}" x2="{LEFT}" y2="{plot_bottom}" stroke="#333"/>',
        svg_text(WIDTH / 2, HEIGHT - 20, x_label, text_anchor="middle", font_family="sans-serif", font_size="14"),
        (
            f'<text x="20" y="{HEIGHT / 2}" text-anchor="middle" '
            f'font-family="sans-serif" font-size="14" '
            f'transform="rotate(-90 20 {HEIGHT / 2})">{html.escape(y_label)}</text>'
        ),
    ]


def scale(value: float, low: float, high: float, start: float, stop: float) -> float:
    if high == low:
        return (start + stop) / 2
    return start + (value - low) * (stop - start) / (high - low)


def distance_figure(rows: list[dict[str, str]], destination: Path) -> None:
    eager_status: dict[int, str] = {}
    if "normalization" in rows[0] and "lazy_configs" in rows[0]:
        parameters = sorted(int(row["n"]) for row in rows)
        lazy_values = {
            int(row["n"]): max(1, int(row["lazy_configs"])) for row in rows
        }
        eager_values = {
            int(row["n"]): max(1, int(row["eager_distance_states"]))
            for row in rows
            if row["eager_distance_states"]
        }
        eager_status = {int(row["n"]): row["eager_status"] for row in rows}
    else:
        relevant = [
            row
            for row in rows
            if row["family"] == "distance" and row["case"] == "positive-lookahead"
        ]
        lazy = {
            int(row["parameter"]): row for row in relevant if row["engine"] == "lazy"
        }
        eager = {
            int(row["parameter"]): row for row in relevant if row["engine"] == "eager"
        }
        parameters = sorted(set(lazy) & set(eager))
        lazy_values = {
            parameter: max(1, int(lazy[parameter]["configurations_discovered"]))
            for parameter in parameters
        }
        eager_values = {}
        for parameter in parameters:
            components = eager[parameter].get("component_dfa_states", "")
            if components:
                eager_values[parameter] = int(components.split(";", 1)[0])
            eager_status[parameter] = eager[parameter]["status"]
    if not parameters:
        raise ValueError("CSV contains no distance rows")
    maximum = max((*lazy_values.values(), *eager_values.values()))
    y_max = max(1, math.ceil(math.log2(maximum)))
    plot_right = WIDTH - RIGHT
    plot_bottom = HEIGHT - BOTTOM

    def x(parameter: int) -> float:
        return scale(parameter, parameters[0], parameters[-1], LEFT, plot_right)

    def y(value: int) -> float:
        return scale(math.log2(value), 0, y_max, plot_bottom, TOP)

    output = frame(
        "distance_n: on-the-fly configurations vs eager component DFA",
        "distance parameter n",
        "states/configurations (log2 scale)",
    )
    for parameter in parameters:
        position = x(parameter)
        output.append(f'<line x1="{position:.2f}" y1="{plot_bottom}" x2="{position:.2f}" y2="{plot_bottom + 5}" stroke="#333"/>')
        output.append(svg_text(position, plot_bottom + 22, parameter, text_anchor="middle", font_family="sans-serif", font_size="11"))
    for exponent in range(y_max + 1):
        position = y(2**exponent)
        output.append(f'<line x1="{LEFT}" y1="{position:.2f}" x2="{plot_right}" y2="{position:.2f}" stroke="#e7e7e7"/>')
        output.append(svg_text(LEFT - 8, position + 4, f"2^{exponent}", text_anchor="end", font_family="sans-serif", font_size="11"))
    lazy_points = [(x(parameter), y(value)) for parameter, value in lazy_values.items()]
    eager_points = [(x(parameter), y(value)) for parameter, value in eager_values.items()]
    output.append(polyline(lazy_points, "#1665a7"))
    output.append(polyline(eager_points, "#c43c39"))
    output.extend(f'<circle cx="{px:.2f}" cy="{py:.2f}" r="3.5" fill="#1665a7"/>' for px, py in lazy_points)
    for parameter, value in eager_values.items():
        px, py = x(parameter), y(value)
        if eager_status.get(parameter) == "resource_limit":
            output.append(f'<path d="M {px - 4:.2f} {py - 4:.2f} L {px + 4:.2f} {py + 4:.2f} M {px + 4:.2f} {py - 4:.2f} L {px - 4:.2f} {py + 4:.2f}" stroke="#c43c39" stroke-width="2"/>')
        else:
            output.append(f'<circle cx="{px:.2f}" cy="{py:.2f}" r="3.5" fill="#c43c39"/>')
    output.append(f'<line x1="{LEFT + 18}" y1="{TOP + 16}" x2="{LEFT + 48}" y2="{TOP + 16}" stroke="#1665a7" stroke-width="2.5"/>')
    output.append(svg_text(LEFT + 56, TOP + 20, "lazy product configurations", font_family="sans-serif", font_size="12"))
    output.append(f'<line x1="{LEFT + 240}" y1="{TOP + 16}" x2="{LEFT + 270}" y2="{TOP + 16}" stroke="#c43c39" stroke-width="2.5"/>')
    output.append(svg_text(LEFT + 278, TOP + 20, "eager distance DFA states", font_family="sans-serif", font_size="12"))
    output.append("</svg>")
    destination.write_text("\n".join(output) + "\n", encoding="utf-8")


def redos_figure(rows: list[dict[str, str]], destination: Path) -> None:
    cases = sorted({row["case"] for row in rows})
    colors = ("#1665a7", "#c43c39", "#3a923a", "#8b5fbf", "#d47b1f")
    measured: dict[tuple[str, str], list[tuple[int, float, bool]]] = {}
    values: list[float] = []
    lengths: list[int] = []
    for row in rows:
        if row["variant"] not in {"positive_lookahead", "linear_control"}:
            continue
        timeout = row["host_result"] == "timeout"
        elapsed = (
            float(row["timeout_seconds"]) * 1000.0
            if timeout
            else max(float(row["match_ms_median"]), 0.0001)
        )
        length = int(row["subject_length"])
        measured.setdefault((row["case"], row["variant"]), []).append(
            (length, elapsed, timeout)
        )
        values.append(elapsed)
        lengths.append(length)
    if not measured:
        raise ValueError("ReDoS CSV contains no plottable rows")
    x_min, x_max = min(lengths), max(lengths)
    log_min = math.floor(math.log10(min(values)))
    log_max = math.ceil(math.log10(max(values)))
    plot_right = WIDTH - RIGHT
    plot_bottom = HEIGHT - BOTTOM

    def x(value: int) -> float:
        return scale(value, x_min, x_max, LEFT, plot_right)

    def y(value: float) -> float:
        return scale(math.log10(value), log_min, log_max, plot_bottom, TOP)

    output = frame(
        "Positive-lookahead ReDoS stress-witness growth",
        "subject length",
        "Python re full-match time (ms, log10 scale)",
    )
    tick_step = max(1, math.ceil((x_max - x_min) / 10))
    for value in range(x_min, x_max + 1, tick_step):
        position = x(value)
        output.append(f'<line x1="{position:.2f}" y1="{plot_bottom}" x2="{position:.2f}" y2="{plot_bottom + 5}" stroke="#333"/>')
        output.append(svg_text(position, plot_bottom + 22, value, text_anchor="middle", font_family="sans-serif", font_size="11"))
    for exponent in range(log_min, log_max + 1):
        position = y(10**exponent)
        output.append(f'<line x1="{LEFT}" y1="{position:.2f}" x2="{plot_right}" y2="{position:.2f}" stroke="#e7e7e7"/>')
        output.append(svg_text(LEFT - 8, position + 4, f"10^{exponent}", text_anchor="end", font_family="sans-serif", font_size="11"))

    for index, case in enumerate(cases):
        color = colors[index % len(colors)]
        for variant, dash in (("positive_lookahead", ""), ("linear_control", "6 4")):
            samples = sorted(measured.get((case, variant), []))
            if not samples:
                continue
            points = [(x(length), y(elapsed)) for length, elapsed, _ in samples]
            output.append(polyline(points, color, dash))
            for (px, py), (_, _, timeout) in zip(points, samples):
                if timeout:
                    output.append(f'<path d="M {px - 4:.2f} {py - 4:.2f} L {px + 4:.2f} {py + 4:.2f} M {px + 4:.2f} {py - 4:.2f} L {px - 4:.2f} {py + 4:.2f}" stroke="{color}" stroke-width="2"/>')
                else:
                    output.append(f'<circle cx="{px:.2f}" cy="{py:.2f}" r="3" fill="{color}"/>')
        legend_x = LEFT + (index % 3) * 235
        legend_y = TOP + 16 + (index // 3) * 18
        output.append(f'<line x1="{legend_x}" y1="{legend_y}" x2="{legend_x + 28}" y2="{legend_y}" stroke="{color}" stroke-width="2.5"/>')
        output.append(svg_text(legend_x + 34, legend_y + 4, case, font_family="sans-serif", font_size="11"))
    output.append(svg_text(LEFT, HEIGHT - 42, "solid: ambiguous positive lookahead; dashed: linear positive-lookahead control; x: timeout", font_family="sans-serif", font_size="11", fill="#444"))
    output.append("</svg>")
    destination.write_text("\n".join(output) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--distance", type=Path)
    parser.add_argument("--redos", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    distance_source = args.distance if args.distance is not None else args.solver
    distance_figure(read_rows(distance_source), args.output_dir / "distance-states.svg")
    redos_figure(read_rows(args.redos), args.output_dir / "redos-growth.svg")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
