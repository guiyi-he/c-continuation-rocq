#!/usr/bin/env python3
"""Render concise paper-facing Markdown tables from the raw experiment CSVs."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path


def read_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as source:
        return list(csv.DictReader(source))


def markdown_table(headers: tuple[str, ...], rows: list[tuple[object, ...]]) -> str:
    def cell(value: object) -> str:
        return str(value).replace("|", "\\|").replace("\n", " ")

    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    lines.extend("| " + " | ".join(cell(value) for value in row) + " |" for row in rows)
    return "\n".join(lines)


def by_engine(rows: list[dict[str, str]]) -> dict[tuple[str, str, str, str], dict[str, str]]:
    return {
        (row["family"], row["case"], row["parameter"], row["engine"]): row
        for row in rows
    }


def eager_states(row: dict[str, str] | None) -> str:
    if row is None:
        return ""
    return row.get("dfa_states_total", "") or row.get("status", "")


def first_component_states(row: dict[str, str] | None) -> str:
    if row is None:
        return ""
    components = row.get("component_dfa_states", "")
    if components:
        return components.split(";", 1)[0]
    return row.get("status", "")


def render_solver(rows: list[dict[str, str]], source: Path) -> str:
    indexed = by_engine(rows)
    status_counts = Counter((row["engine"], row["status"]) for row in rows)
    first = rows[0]
    sections = [
        "# REwPLA experimental evaluation summary",
        "",
        "This report is derived from raw CSV; censored outcomes remain explicit.",
        "",
        "## Provenance",
        "",
        f"- Source: `{source}`",
        f"- Suite version: `{first.get('suite_version', '')}`",
        f"- Solver: `{first.get('solver_version', '')}`",
        f"- Git revision: `{first.get('git_revision', '')}` (dirty: `{first.get('git_dirty', '')}`)",
        f"- Compiler: `{first.get('compiler', '')}`",
        f"- Platform: `{first.get('platform', '')}`",
        "",
        "## Outcome accounting",
        "",
        markdown_table(
            ("engine", "status", "rows"),
            [(engine, status, count) for (engine, status), count in sorted(status_counts.items())],
        ),
        "",
        "## Native distance family",
        "",
    ]

    distance_rows: list[tuple[object, ...]] = []
    parameters = sorted(
        {
            int(row["parameter"])
            for row in rows
            if row["family"] == "distance" and row["case"] == "positive-lookahead"
        }
    )
    for parameter in parameters:
        key = ("distance", "positive-lookahead", str(parameter))
        lazy = indexed.get((*key, "lazy"))
        eager = indexed.get((*key, "eager"))
        distance_rows.append(
            (
                parameter,
                lazy.get("status", "") if lazy else "",
                lazy.get("witness_length", "") if lazy else "",
                lazy.get("configurations_discovered", "") if lazy else "",
                first_component_states(eager),
                lazy.get("solve_ms_median", "") if lazy else "",
                eager.get("solve_ms_median", "") if eager else "",
            )
        )
    sections.extend(
        [
            markdown_table(
                (
                    "n",
                    "status",
                    "witness len",
                    "lazy configs",
                    "eager DFA states/status",
                    "lazy ms",
                    "eager ms",
                ),
                distance_rows,
            ),
            "",
            "## Paper-family scale points",
            "",
        ]
    )

    family_rows: list[tuple[object, ...]] = []
    selected = sorted(
        {
            (row["family"], row["case"], row["parameter"])
            for row in rows
            if (
                row["family"] in {"tight-family", "lookahead-topology"}
                and row["case"] in {"generic-solver", "periodic-conjunction"}
            )
        }
    )
    for family, case, parameter in selected:
        lazy = indexed.get((family, case, parameter, "lazy"))
        eager = indexed.get((family, case, parameter, "eager"))
        family_rows.append(
            (
                family,
                case,
                parameter,
                lazy.get("configurations_discovered", "") if lazy else "",
                eager_states(eager),
                eager.get("status", "") if eager else "",
            )
        )
    sections.extend(
        [
            markdown_table(
                ("family", "case", "parameter", "lazy configs", "eager states", "eager status"),
                family_rows,
            ),
            "",
            "## Lookahead topology controls",
            "",
        ]
    )

    topology_rows: list[tuple[object, ...]] = []
    for row in rows:
        if row["engine"] != "lazy" or row["case"] not in {
            "nested-chain",
            "constraint-width",
            "fixed-width",
        }:
            continue
        eager = indexed.get((row["family"], row["case"], row["parameter"], "eager"))
        topology_rows.append(
            (
                row["case"],
                row["parameter"],
                row.get("lookahead_depth", ""),
                row.get("constraint_width", ""),
                row.get("configurations_discovered", ""),
                eager_states(eager),
            )
        )
    sections.append(
        markdown_table(
            ("case", "parameter", "LA depth", "constraint width", "lazy configs", "eager states"),
            topology_rows,
        )
    )
    ordinary_rows: list[tuple[object, ...]] = []
    for row in rows:
        if row["engine"] != "lazy" or row["case"] not in {
            "star-depth",
            "alphabet-size",
        }:
            continue
        eager = indexed.get((row["family"], row["case"], row["parameter"], "eager"))
        ordinary_rows.append(
            (
                row["case"],
                row["parameter"],
                row.get("alphabet_size", ""),
                row.get("star_depth", ""),
                row.get("configurations_discovered", ""),
                eager_states(eager),
            )
        )
    sections.extend(
        [
            "",
            "## Ordinary-regex controls",
            "",
            markdown_table(
                ("case", "parameter", "alphabet size", "star depth", "lazy configs", "eager states"),
                ordinary_rows,
            ),
        ]
    )
    return "\n".join(sections) + "\n"


def render_redos(rows: list[dict[str, str]], source: Path) -> str:
    sections = [
        "",
        "## Defensive ReDoS case study",
        "",
        f"Raw source: `{source}`. Timings are standard-engine observations, not semantic proofs.",
        "",
    ]
    output: list[tuple[object, ...]] = []
    for case in sorted({row["case"] for row in rows}):
        case_rows = [row for row in rows if row["case"] == case]
        repetitions = sorted({int(row["repetitions"]) for row in case_rows})
        for repetition in repetitions:
            positive = next(
                row
                for row in case_rows
                if int(row["repetitions"]) == repetition
                and row["variant"] == "positive_lookahead"
            )
            control = next(
                row
                for row in case_rows
                if int(row["repetitions"]) == repetition
                and row["variant"] == "linear_control"
            )
            output.append(
                (
                    case,
                    positive.get("category", ""),
                    positive.get("certified", ""),
                    repetition,
                    positive["subject_length"],
                    positive["ambiguity_log2_lower_bound"],
                    positive["host_result"],
                    positive["match_ms_median"] or f">={positive['timeout_seconds']}s",
                    control["match_ms_median"],
                    positive["overlap_solve_ms"],
                    positive.get("probe_wall_ms_median", ""),
                    positive.get("peak_rss_mib_median", ""),
                )
            )
    sections.append(
        markdown_table(
            (
                "case",
                "category",
                "certified",
                "n",
                "subject len",
                "log2 branch lower bound",
                "host result",
                "positive-LA ms",
                "linear control ms",
                "solver overlap ms",
                "probe wall ms",
                "peak RSS MiB",
            ),
            output,
        )
    )
    return "\n".join(sections) + "\n"


def render_dnf(
    compact_rows: list[dict[str, str]],
    dnf_rows: list[dict[str, str]],
    source: Path,
) -> str:
    compact = by_engine(compact_rows)
    output: list[tuple[object, ...]] = []
    for row in dnf_rows:
        key = (row["family"], row["case"], row["parameter"], row["engine"])
        baseline = compact.get(key)
        output.append(
            (
                row["family"],
                row["case"],
                row["parameter"],
                row["status"],
                baseline.get("ast_nodes", "") if baseline else "",
                row.get("ast_nodes", ""),
                baseline.get("solve_ms_median", "") if baseline else "",
                row.get("solve_ms_median", ""),
            )
        )
    return "\n".join(
        [
            "",
            "## Compact representation versus distributive DNF",
            "",
            f"DNF source: `{source}`. Both modes are required to return the same status and witness.",
            "",
            markdown_table(
                (
                    "family",
                    "case",
                    "parameter",
                    "status",
                    "compact AST",
                    "DNF AST",
                    "compact ms",
                    "DNF ms",
                ),
                output,
            ),
        ]
    ) + "\n"


def render_distance_bench(rows: list[dict[str, str]], source: Path) -> str:
    output = [
        (
            row["n"],
            row["expected"],
            row["lazy_status"],
            row["lazy_configs"],
            row["lazy_ms"],
            row["eager_status"],
            row["eager_distance_states"],
            row["eager_ms"],
        )
        for row in rows
    ]
    return "\n".join(
        [
            "",
            "## Extended native distance sweep",
            "",
            f"Raw source: `{source}`. The eager per-component cap is retained as a censored outcome.",
            "",
            markdown_table(
                (
                    "n",
                    "expected",
                    "lazy status",
                    "lazy configs",
                    "lazy ms",
                    "eager status",
                    "eager distance states",
                    "eager ms",
                ),
                output,
            ),
        ]
    ) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--distance", type=Path)
    parser.add_argument("--dnf", type=Path)
    parser.add_argument("--redos", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    solver_rows = read_rows(args.solver)
    if not solver_rows:
        raise SystemExit("solver CSV has no data rows")
    report = render_solver(solver_rows, args.solver)
    if args.distance is not None:
        distance_rows = read_rows(args.distance)
        if not distance_rows:
            raise SystemExit("distance CSV has no data rows")
        report += render_distance_bench(distance_rows, args.distance)
    if args.dnf is not None:
        dnf_rows = read_rows(args.dnf)
        if not dnf_rows:
            raise SystemExit("DNF CSV has no data rows")
        report += render_dnf(solver_rows, dnf_rows, args.dnf)
    if args.redos is not None:
        redos_rows = read_rows(args.redos)
        if not redos_rows:
            raise SystemExit("ReDoS CSV has no data rows")
        report += render_redos(redos_rows, args.redos)

    if args.output is None:
        print(report, end="")
    else:
        args.output.write_text(report, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
