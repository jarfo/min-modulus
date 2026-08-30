#!/usr/bin/env python3
"""Generate kernel-checked normalized five-coordinate SHC certificates.

The search uses Torch to greedily choose a compact set of dissociation or
head-2 witnesses for each fixed pair of initial coordinates.  The emitted
Lean files contain `by decide` proofs of both relation validity and complete
coverage, so this script and Torch are outside the trusted proof base.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

import torch


def relation_rows() -> list[tuple[tuple[int, ...], int]]:
    """All oriented dissociation rows followed by all legal head-2 rows."""
    rows: list[tuple[tuple[int, ...], int]] = []
    for coeffs in itertools.product((-1, 0, 1), repeat=5):
        if all(c == 0 for c in coeffs):
            continue
        if next(c for c in coeffs if c) != 1:
            continue
        positive = tuple(i for i, c in enumerate(coeffs) if c == 1)
        negative = tuple(i for i, c in enumerate(coeffs) if c == -1)
        code = sum(1 << i for i in positive) + 32 * sum(1 << i for i in negative)
        rows.append((coeffs, code))

    for head in range(5):
        others = [i for i in range(5) if i != head]
        for states in itertools.product((-1, 0, 1), repeat=4):
            positive = tuple(i for i, state in zip(others, states) if state == 1)
            negative = tuple(i for i, state in zip(others, states) if state == -1)
            if len(positive) + 1 > len(negative):
                continue
            row = [0] * 5
            row[head] = 2
            for i in positive:
                row[i] = 1
            for i in negative:
                row[i] = -1
            data = sum(1 << i for i in positive) + 32 * sum(1 << i for i in negative)
            rows.append((tuple(row), 1024 + head + 5 * data))
    return rows


def greedy_codes(
    modulus: int,
    first: int,
    rows: list[tuple[tuple[int, ...], int]],
    row_tensor: torch.Tensor,
) -> list[int]:
    candidates = torch.tensor(
        [
            (1, first, second, third, fourth)
            for second, third, fourth in itertools.combinations(range(first + 1, modulus), 3)
        ],
        dtype=torch.int32,
    )
    hits = torch.remainder(candidates @ row_tensor.T, modulus) == 0
    uncovered = torch.ones(len(candidates), dtype=torch.bool)
    chosen: list[int] = []
    while bool(torch.any(uncovered)):
        counts = torch.sum(hits[uncovered], dim=0)
        best = int(torch.argmax(counts))
        if int(counts[best]) == 0:
            raise RuntimeError(f"uncovered shard at N={modulus}, a={first}")
        chosen.append(rows[best][1])
        uncovered &= ~hits[:, best]
    return chosen


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def shard_source(
    modulus: int,
    a_offset: int,
    codes: list[int],
) -> str:
    n = modulus - 2
    a_bound = modulus - 5
    lines = [
        f"import MinModulus.SHCFiveCertificate\n\n",
        "namespace MinModulus.SHCFiveCertificate.Generated\n\n",
        "set_option maxRecDepth 1000000\n",
        "set_option maxHeartbeats 1000000000\n\n",
    ]
    suffix = f"{a_offset:02d}"
    lines.extend(
        [
            f"private def codes{modulus}_{suffix} : List ℕ := {lean_list(codes)}\n\n",
            f"private theorem valid{modulus}_{suffix} : ∀ code ∈ codes{modulus}_{suffix}, "
            "validRelationCode code := by\n  decide\n\n",
            f"private theorem cover{modulus}_{suffix} : ∀ q : IncreasingFourTail {n} "
            f"(⟨{a_offset}, by norm_num⟩ : Fin {a_bound}),\n",
            f"    coveredNat {modulus} codes{modulus}_{suffix} "
            f"(increasingFourValues (N := {modulus}) "
            f"⟨⟨{a_offset}, by norm_num⟩, q⟩) = true := by\n",
            "  decide\n\n",
            f"theorem certificate{modulus}_a{a_offset:02d}\n",
            f"    (q : IncreasingFourTail {n} "
            f"(⟨{a_offset}, by norm_num⟩ : Fin {a_bound})) : ∃ code,\n",
            "      validRelationCode code ∧\n",
            f"      relationZeroNat {modulus} (increasingFourValues "
            f"(N := {modulus}) ⟨⟨{a_offset}, by norm_num⟩, q⟩) code = true := by\n",
            f"  exact coveredNat_exists_valid {modulus} codes{modulus}_{suffix} _ "
            f"valid{modulus}_{suffix} (cover{modulus}_{suffix} q)\n",
        ]
    )
    lines.append("\nend MinModulus.SHCFiveCertificate.Generated\n")
    return "".join(lines)


def aggregate_source(modulus: int) -> str:
    count = modulus - 5
    imports = "".join(
        f"import MinModulus.Generated.SHCFiveN{modulus}A{offset:02d}\n"
        for offset in range(count)
    )
    lines = [
        imports,
        "\nnamespace MinModulus.SHCFiveCertificate.Generated\n\n",
        f"theorem certificate{modulus} : Certificate {modulus} := by\n",
        "  intro q\n",
        "  rcases q with ⟨a, tail⟩\n",
        "  fin_cases a\n",
    ]
    for offset in range(count):
        lines.append(f"  · exact certificate{modulus}_a{offset:02d} tail\n")
    lines.append("\nend MinModulus.SHCFiveCertificate.Generated\n")
    return "".join(lines)


def generate(modulus: int, output: Path) -> tuple[int, int]:
    if modulus < 35 or modulus % 2 == 0:
        raise ValueError("modulus must be odd and at least 35")
    output.mkdir(parents=True, exist_ok=True)
    rows = relation_rows()
    row_tensor = torch.tensor([row for row, _code in rows], dtype=torch.int32)
    total_codes = 0
    for a_offset in range(modulus - 5):
        first = a_offset + 2
        codes = greedy_codes(modulus, first, rows, row_tensor)
        total_codes += len(codes)
        path = output / f"SHCFiveN{modulus}A{a_offset:02d}.lean"
        path.write_text(shard_source(modulus, a_offset, codes), encoding="utf-8")
    (output / f"SHCFiveN{modulus}.lean").write_text(
        aggregate_source(modulus), encoding="utf-8"
    )
    return modulus - 5, total_codes


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--modulus", type=int, required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "MinModulus" / "Generated",
    )
    args = parser.parse_args()
    shards, codes = generate(args.modulus, args.output)
    print(f"N={args.modulus}: wrote {shards} shards containing {codes} relation codes")


if __name__ == "__main__":
    main()
