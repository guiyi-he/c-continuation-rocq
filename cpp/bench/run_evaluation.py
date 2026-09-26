#!/usr/bin/env python3
"""Run the correctness gates and paper-oriented experiment profiles."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import platform
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run_logged(
    name: str,
    command: list[str],
    cwd: Path,
    log,
    manifest_commands: list[dict[str, object]],
) -> None:
    started = time.perf_counter()
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - started
    log.write(f"\n===== {name} =====\n")
    log.write(f"command: {json.dumps(command)}\n")
    log.write(completed.stdout)
    log.flush()
    manifest_commands.append(
        {
            "name": name,
            "command": command,
            "returncode": completed.returncode,
            "elapsed_seconds": elapsed,
        }
    )
    if completed.returncode != 0:
        raise RuntimeError(f"{name} failed; see correctness.log")


def capture_csv(command: list[str], cwd: Path, destination: Path) -> float:
    started = time.perf_counter()
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    elapsed = time.perf_counter() - started
    if completed.returncode != 0:
        raise RuntimeError(
            f"experiment failed: {command}\n{completed.stderr.strip()}"
        )
    destination.write_text(completed.stdout, encoding="utf-8")
    return elapsed


def command_output(command: list[str], cwd: Path) -> str:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unavailable"


def validate_dnf_agreement(compact_path: Path, dnf_path: Path) -> None:
    with compact_path.open(newline="", encoding="utf-8") as source:
        compact_rows = list(csv.DictReader(source))
    with dnf_path.open(newline="", encoding="utf-8") as source:
        dnf_rows = list(csv.DictReader(source))
    compact = {
        (row["family"], row["case"], row["parameter"], row["engine"]): row
        for row in compact_rows
    }
    censored = {"resource_limit", "timeout"}
    for dnf in dnf_rows:
        key = (dnf["family"], dnf["case"], dnf["parameter"], dnf["engine"])
        baseline = compact.get(key)
        if baseline is None:
            continue
        if dnf["status"] in censored or baseline["status"] in censored:
            continue
        if (dnf["status"], dnf["witness"]) != (
            baseline["status"],
            baseline["witness"],
        ):
            raise RuntimeError(
                f"compact/DNF disagreement for {'/'.join(key[:3])}: "
                f"compact=({baseline['status']}, {baseline['witness']!r}), "
                f"dnf=({dnf['status']}, {dnf['witness']!r})"
            )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).parents[2])
    parser.add_argument("--profile", choices=("smoke", "full"), default="smoke")
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    cpp = repo / "cpp"
    executable_suffix = ".exe" if platform.system() == "Windows" else ""
    solver = cpp / "build" / f"rewpla-solver{executable_suffix}"
    redos = cpp / "build" / f"rewpla-redos{executable_suffix}"
    unit = cpp / "build" / f"rewpla-solver-tests{executable_suffix}"
    distance_bench = cpp / "build" / f"rewpla-distance-bench{executable_suffix}"
    redos_corpus = cpp / "bench" / "redos_cases.json"
    for executable in (solver, redos, unit, distance_bench):
        if not executable.is_file():
            raise SystemExit(f"missing executable; run make -C cpp first: {executable}")

    if args.output_dir is None:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        output = cpp / "build" / f"evaluation-{args.profile}-{stamp}"
    else:
        output = args.output_dir
        if not output.is_absolute():
            output = repo / output
    if output.exists():
        if not args.overwrite:
            raise SystemExit(f"output directory already exists: {output}")
        resolved = output.resolve()
        build_root = (cpp / "build").resolve()
        if resolved == build_root or build_root not in resolved.parents:
            raise SystemExit("--overwrite is restricted to a child of cpp/build")
        shutil.rmtree(resolved)
    output.mkdir(parents=True)

    commands: list[dict[str, object]] = []
    correctness_log = output / "correctness.log"
    with correctness_log.open("w", encoding="utf-8") as log:
        if args.profile == "full":
            run_logged(
                "complete Rocq/OCaml regression suite",
                ["make", "test"],
                repo,
                log,
                commands,
            )
        else:
            run_logged(
                "distance-and-topology Rocq theorems",
                [
                    "rocq",
                    "compile",
                    "-Q",
                    "theories",
                    "CCont",
                    "theories/DistanceBenchmark.v",
                ],
                repo,
                log,
                commands,
            )
        run_logged("C++ unit tests", [str(unit)], repo, log, commands)
        run_logged(
            "solver CLI smoke",
            [sys.executable, str(cpp / "tests" / "cli_smoke.py"), str(solver)],
            repo,
            log,
            commands,
        )
        frontend_differential = [
            sys.executable,
            str(cpp / "tests" / "regex_frontend_differential.py"),
            str(solver),
        ]
        if args.profile == "full":
            frontend_differential += [
                "--random-patterns",
                "100",
                "--seed",
                "20260926",
            ]
        run_logged(
            "real-regex differential",
            frontend_differential,
            repo,
            log,
            commands,
        )
        run_logged(
            "ReDoS application smoke",
            [sys.executable, str(cpp / "tests" / "redos_smoke.py"), str(redos)],
            repo,
            log,
            commands,
        )
        differential = [
            sys.executable,
            str(cpp / "tests" / "differential.py"),
            str(solver),
        ]
        if args.profile == "full":
            differential += [
                "--random-cases",
                "200",
                "--seed",
                "20260926",
                "--word-bound",
                "4",
            ]
        run_logged("extracted-OCaml alignment", differential, repo, log, commands)

    suite_command = [
        sys.executable,
        str(cpp / "bench" / "benchmark_suite.py"),
        str(solver),
    ]
    if args.profile == "smoke":
        suite_command += [
            "--families",
            "distance,periodic,topology,ordinary,tight,intersection",
            "--distance-range",
            "0:3",
            "--period-sets",
            "2,2+3",
            "--topology-range",
            "1:2",
            "--ordinary-range",
            "1:2",
            "--tight-range",
            "2:2",
            "--intersection-range",
            "1:2",
        ]
    else:
        suite_command += ["--warmup", "1", "--repeat", "5", "--timeout", "60"]
    solver_csv = output / "solver-results.csv"
    suite_seconds = capture_csv(suite_command, repo, solver_csv)

    distance_command = [
        str(distance_bench),
        "--max-n",
        "8" if args.profile == "smoke" else "20",
        "--repeat",
        "1" if args.profile == "smoke" else "5",
    ]
    if args.profile == "full":
        distance_command += ["--warmup", "1"]
    distance_csv = output / "distance-results.csv"
    distance_seconds = capture_csv(distance_command, repo, distance_csv)

    dnf_command = [
        sys.executable,
        str(cpp / "bench" / "benchmark_suite.py"),
        str(solver),
        "--families",
        "distance,topology",
        "--engines",
        "lazy",
        "--normalization",
        "dnf",
    ]
    if args.profile == "smoke":
        dnf_command += [
            "--distance-range",
            "0:3",
            "--topology-range",
            "1:2",
        ]
    else:
        dnf_command += [
            "--distance-range",
            "0:10",
            "--topology-range",
            "1:8",
            "--warmup",
            "1",
            "--repeat",
            "5",
            "--timeout",
            "60",
        ]
    dnf_csv = output / "solver-dnf-results.csv"
    dnf_seconds = capture_csv(dnf_command, repo, dnf_csv)
    validate_dnf_agreement(solver_csv, dnf_csv)

    redos_command = [
        sys.executable,
        str(cpp / "bench" / "redos_case_study.py"),
        str(redos),
    ]
    if args.profile == "smoke":
        redos_command += ["--max-repetitions", "4", "--repeat", "1", "--timeout", "2"]
    else:
        redos_command += ["--warmup", "1", "--repeat", "5", "--timeout", "2"]
    redos_csv = output / "redos-results.csv"
    redos_seconds = capture_csv(redos_command, repo, redos_csv)

    summary = output / "SUMMARY.md"
    subprocess.run(
        [
            sys.executable,
            str(cpp / "bench" / "summarize_results.py"),
            "--solver",
            str(solver_csv),
            "--redos",
            str(redos_csv),
            "--dnf",
            str(dnf_csv),
            "--distance",
            str(distance_csv),
            "--output",
            str(summary),
        ],
        cwd=repo,
        check=True,
    )
    subprocess.run(
        [
            sys.executable,
            str(cpp / "bench" / "plot_results.py"),
            "--solver",
            str(solver_csv),
            "--distance",
            str(distance_csv),
            "--redos",
            str(redos_csv),
            "--output-dir",
            str(output),
        ],
        cwd=repo,
        check=True,
    )

    manifest = {
        "profile": args.profile,
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "repo": str(repo),
        "git_revision": command_output(["git", "rev-parse", "HEAD"], repo),
        "git_status": command_output(["git", "status", "--porcelain"], repo),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "solver_version": command_output([str(solver), "--version"], repo),
        "redos_version": command_output([str(redos), "--version"], repo),
        "solver_sha256": sha256(solver),
        "redos_sha256": sha256(redos),
        "redos_corpus": str(redos_corpus),
        "redos_corpus_sha256": sha256(redos_corpus),
        "distance_bench_sha256": sha256(distance_bench),
        "correctness_commands": commands,
        "solver_suite_command": suite_command,
        "solver_suite_seconds": suite_seconds,
        "distance_command": distance_command,
        "distance_seconds": distance_seconds,
        "dnf_command": dnf_command,
        "dnf_seconds": dnf_seconds,
        "redos_command": redos_command,
        "redos_seconds": redos_seconds,
        "artifacts": [
            correctness_log.name,
            solver_csv.name,
            distance_csv.name,
            dnf_csv.name,
            redos_csv.name,
            summary.name,
            "distance-states.svg",
            "redos-growth.svg",
        ],
    }
    (output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
