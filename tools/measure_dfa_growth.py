"""Measure the existing ccont CLI for the E_n example family."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from dfa_growth_model import family


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, nargs="+", default=[1, 2, 3, 4])
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--output-dir", type=Path, default=Path("experiments/dfa_growth"))
    parser.add_argument("--exe", type=Path, default=Path("_build/default/cli/ccont.exe"))
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    binary = args.exe.resolve()
    if not binary.is_file():
        raise SystemExit("Build ccont with opam exec -- dune build cli/ccont.exe first")
    binary_hash = hashlib.sha256(binary.read_bytes()).hexdigest()
    results_path = args.output_dir / "cli_measurements.json"
    results = json.loads(results_path.read_text(encoding="utf-8")) if results_path.exists() else []
    for n in args.n:
        alphabet, expression, width = family(n)
        target = args.output_dir / f"cli_n{n}.json"
        command = [str(binary), "--automaton", "rewpla", "--alphabet", alphabet,
                   "--format", "json", "-o", str(target), expression]
        entry = dict(n=n, alphabet=alphabet, expression=expression,
                     alphabetic_width=width, expression_characters=len(expression),
                     binary_sha256=binary_hash, command=command, timeout_seconds=args.timeout)
        print(json.dumps(dict(event="started", n=n, width=width)), flush=True)
        started = time.perf_counter()
        try:
            result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    timeout=args.timeout)
            entry.update(returncode=result.returncode, elapsed_seconds=time.perf_counter() - started,
                         stdout=result.stdout.decode("utf-8", errors="replace"),
                         stderr=result.stderr.decode("utf-8", errors="replace"))
            if result.returncode == 0:
                data = json.loads(target.read_text(encoding="utf-8"))
                entry.update(status="complete", structural_states=data["state_count"],
                             transitions=len(data["transitions"]), method=data["method"],
                             output_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
            else:
                entry["status"] = "state_limit" if "10000 states" in entry["stderr"] else "error"
        except subprocess.TimeoutExpired:
            entry.update(status="timeout", elapsed_seconds=time.perf_counter() - started)
        results = [old for old in results if old["n"] != n] + [entry]
        results.sort(key=lambda item: item["n"])
        results_path.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n",
                                encoding="utf-8", newline="\n")
        print(json.dumps({k: entry[k] for k in ("n", "status", "elapsed_seconds", "structural_states")
                          if k in entry}), flush=True)


if __name__ == "__main__":
    main()
