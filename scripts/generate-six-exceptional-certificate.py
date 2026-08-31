#!/usr/bin/env python3
"""Generate the kernel-checked normalized order-105 generator certificate.

The distinguished coordinate is 3.  The other five values are increasing
selections from the 55 nonunits above 3.  For each fixed pair of initial tail
indices, Torch finds a decision tree of subset-collision/head-2 witnesses.
Symbolic branches use only relations independent of the remaining coordinates;
the emitted Lean files check every relation with ordinary kernel reduction.
Generated block imports form two dependency lanes so fresh Lake builds never
compile more than two certificate blocks concurrently.
This script and Torch remain outside the trusted base.
"""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

import torch


MODULUS = 105
COORDINATES = 6
BUILD_LANES = 2
TAIL_VALUES = [x for x in range(4, MODULUS) if math.gcd(x, MODULUS) != 1]


def write_generated(path: Path, source: str) -> None:
    if path.exists() and path.read_text(encoding="utf-8") == source:
        return
    path.write_text(source, encoding="utf-8")


def relation_rows() -> list[tuple[tuple[int, ...], int]]:
    rows: list[tuple[tuple[int, ...], int]] = []
    for coeffs in itertools.product((-1, 0, 1), repeat=COORDINATES):
        if all(c == 0 for c in coeffs):
            continue
        if next(c for c in coeffs if c) != 1:
            continue
        positive = tuple(i for i, c in enumerate(coeffs) if c == 1)
        negative = tuple(i for i, c in enumerate(coeffs) if c == -1)
        code = sum(1 << i for i in positive) + 64 * sum(1 << i for i in negative)
        rows.append((coeffs, code))
    for head in range(COORDINATES):
        others = [i for i in range(COORDINATES) if i != head]
        for states in itertools.product((-1, 0, 1), repeat=COORDINATES - 1):
            positive = tuple(i for i, state in zip(others, states) if state == 1)
            negative = tuple(i for i, state in zip(others, states) if state == -1)
            if len(positive) + 1 > len(negative):
                continue
            row = [0] * COORDINATES
            row[head] = 2
            for i in positive:
                row[i] = 1
            for i in negative:
                row[i] = -1
            data = sum(1 << i for i in positive) + 64 * sum(1 << i for i in negative)
            rows.append((tuple(row), 4096 + head + COORDINATES * data))
    return rows


def choose_tree(
    first: int,
    second: int,
    rows: list[tuple[tuple[int, ...], int]],
    row_tensor: torch.Tensor,
) -> tuple[list[tuple[int | None, list[tuple[int | None, list[int]]]]], int]:
    tails = list(itertools.combinations(range(second + 1, len(TAIL_VALUES)), 3))
    candidates = torch.tensor(
        [
            (3, TAIL_VALUES[first], TAIL_VALUES[second], *(TAIL_VALUES[i] for i in rest))
            for rest in tails
        ],
        dtype=torch.int32,
    )
    hits = torch.remainder(candidates @ row_tensor.T, MODULUS) == 0
    remaining = len(TAIL_VALUES) - second - 1
    candidate_index: dict[tuple[int, int, int], int] = {}
    for index, rest in enumerate(tails):
        c = rest[0] - second - 1
        d = rest[1] - rest[0] - 1
        e = rest[2] - rest[1] - 1
        candidate_index[c, d, e] = index

    independent_from = [
        torch.tensor(
            [all(coefficient == 0 for coefficient in row[start:]) for row, _code in rows],
            dtype=torch.bool,
        )
        for start in range(COORDINATES + 1)
    ]

    def common_code(indices: list[int], variable_from: int) -> int | None:
        common = torch.all(hits[indices], dim=0) & independent_from[variable_from]
        if not bool(torch.any(common)):
            return None
        return rows[int(torch.argmax(common.to(torch.int8)))][1]

    tree: list[tuple[int | None, list[tuple[int | None, list[int]]]]] = []
    branches = 0
    for c in range(remaining - 2):
        c_indices = [
            candidate_index[c, d, e]
            for d in range(remaining - c - 2)
            for e in range(remaining - c - d - 2)
        ]
        code_c = common_code(c_indices, 4)
        if code_c is not None:
            tree.append((code_c, []))
            branches += 1
            continue
        by_d: list[tuple[int | None, list[int]]] = []
        for d in range(remaining - c - 2):
            d_indices = [
                candidate_index[c, d, e]
                for e in range(remaining - c - d - 2)
            ]
            code_d = common_code(d_indices, 5)
            if code_d is not None:
                by_d.append((code_d, []))
                branches += 1
                continue
            leaf_codes = []
            for index in d_indices:
                matching = hits[index]
                if not bool(torch.any(matching)):
                    bad = candidates[index].tolist()
                    raise RuntimeError(f"uncovered block ({first}, {second}): {bad}")
                leaf_codes.append(rows[int(torch.argmax(matching.to(torch.int8)))][1])
            by_d.append((None, leaf_codes))
            branches += len(leaf_codes)
        tree.append((None, by_d))
    return tree, branches


def block_source(
    first: int,
    offset: int,
    second: int,
    tree: list[tuple[int | None, list[tuple[int | None, list[int]]]]],
    predecessor: str | None,
) -> str:
    suffix = f"{first:02d}_{offset:02d}"
    remaining = len(TAIL_VALUES) - second - 1
    lines = [
        f"import {predecessor or 'MinModulus.SHCSixExceptionalCertificate'}\n\n",
        "namespace MinModulus.SHCSixExceptionalCertificate.Generated\n\n",
        "set_option maxRecDepth 1000000\n",
        "set_option maxHeartbeats 1000000000\n\n",
    ]
    for third, (code_c, by_d) in enumerate(tree):
        tail_type = (
            f"Σ d : Fin ({remaining} - {third} - 2), "
            f"Fin ({remaining} - ({third} + 1 + d.val) - 1)"
        )
        theorem = f"certificate105_a{first:02d}_b{offset:02d}_c{third:02d}"
        lines.extend(
            [
                f"private theorem {theorem} (q : {tail_type}) : ∃ code,\n",
                "    validRelationCode code ∧\n",
                f"    relationZeroNat (blockValues (⟨{first}, by norm_num⟩ : Fin 55) "
                f"(⟨{second}, by norm_num⟩ : Fin 55) "
                f"⟨(⟨{third}, by norm_num⟩ : Fin ({remaining} - 2)), q⟩) "
                "code = true := by\n",
            ]
        )
        if code_c is not None:
            lines.append(
                f"  exact ⟨{code_c}, by decide, by simp +decide "
                "[relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩\n\n"
            )
            continue
        lines.extend(["  rcases q with ⟨d, e⟩\n", "  fin_cases d\n"])
        for code_d, leaf_codes in by_d:
            if code_d is not None:
                lines.append(
                    f"  · exact ⟨{code_d}, by decide, by simp +decide "
                    "[relationZeroNat, blockValues, maskSumNat, nonunit105Value]⟩\n"
                )
                continue
            lines.append("  · fin_cases e\n")
            for code in leaf_codes:
                lines.append(f"    · exact ⟨{code}, by decide, by decide⟩\n")
        lines.append("\n")
    lines.extend(
        [
            f"theorem certificate105_a{first:02d}_b{offset:02d} "
            f"(q : IncreasingThree {remaining}) : ∃ code,\n",
            "    validRelationCode code ∧\n",
            f"    relationZeroNat (blockValues (⟨{first}, by norm_num⟩ : Fin 55) "
            f"(⟨{second}, by norm_num⟩ : Fin 55) q) code = true := by\n",
            "  rcases q with ⟨c, q⟩\n",
            "  fin_cases c\n",
        ]
    )
    for third in range(remaining - 2):
        lines.append(
            f"  · exact certificate105_a{first:02d}_b{offset:02d}_c{third:02d} q\n"
        )
    lines.append("\nend MinModulus.SHCSixExceptionalCertificate.Generated\n")
    return "".join(lines)


def shard_source(first: int, blocks: list[tuple[int, int]]) -> str:
    imports = "".join(
        f"import MinModulus.Generated.SHCSixN105A{first:02d}B{offset:02d}\n"
        for offset, _second in blocks
    )
    lines = [
        imports,
        "\n",
        "namespace MinModulus.SHCSixExceptionalCertificate.Generated\n\n",
        "set_option maxRecDepth 1000000\n",
        "set_option maxHeartbeats 1000000000\n\n",
    ]
    lines.extend(
        [
            f"theorem certificate105_a{first:02d}\n",
            f"    (q : IncreasingFiveTail 55 (⟨{first}, by norm_num⟩ : Fin 51)) : ∃ code,\n",
            "      validRelationCode code ∧\n",
            f"      relationZeroNat (values ⟨(⟨{first}, by norm_num⟩ : Fin 51), q⟩) code = true := by\n",
            "  rcases q with ⟨b, c, d, e⟩\n",
            "  fin_cases b\n",
        ]
    )
    for offset, second in blocks:
        remaining = len(TAIL_VALUES) - second - 1
        lines.extend(
            [
                f"  · let c' : Fin ({remaining} - 2) := "
                "⟨c.val, by have hc := c.isLt; dsimp only at hc; omega⟩\n",
                f"    let d' : Fin ({remaining} - c'.val - 2) := "
                "⟨d.val, by have hd := d.isLt; dsimp only at hd; dsimp [c']; omega⟩\n",
                f"    let e' : Fin ({remaining} - (c'.val + 1 + d'.val) - 1) := "
                "⟨e.val, by have he := e.isLt; dsimp only at he; "
                "dsimp [c', d']; omega⟩\n",
                f"    let q' : IncreasingThree {remaining} := ⟨c', d', e'⟩\n",
                f"    have hv : values ⟨(⟨{first}, by norm_num⟩ : Fin 51), "
                f"⟨⟨{offset}, by norm_num⟩, c, d, e⟩⟩ =\n",
                f"        blockValues (⟨{first}, by norm_num⟩ : Fin 55) "
                f"(⟨{second}, by norm_num⟩ : Fin 55) q' := by\n",
                "      funext i\n",
                "      fin_cases i <;> rfl\n",
                "    rw [hv]\n",
                f"    exact certificate105_a{first:02d}_b{offset:02d} q'\n",
            ]
        )
    lines.append("\nend MinModulus.SHCSixExceptionalCertificate.Generated\n")
    return "".join(lines)


def aggregate_source() -> str:
    imports = "".join(
        f"import MinModulus.Generated.SHCSixN105A{first:02d}\n" for first in range(51)
    )
    lines = [
        imports,
        "\nnamespace MinModulus.SHCSixExceptionalCertificate.Generated\n\n",
        "theorem certificate105 : Certificate := by\n",
        "  intro q\n",
        "  rcases q with ⟨a, tail⟩\n",
        "  fin_cases a\n",
    ]
    for first in range(51):
        lines.append(f"  · exact certificate105_a{first:02d} tail\n")
    lines.append("\nend MinModulus.SHCSixExceptionalCertificate.Generated\n")
    return "".join(lines)


def generate(output: Path, only_first: int | None = None) -> tuple[int, int, int]:
    output.mkdir(parents=True, exist_ok=True)
    rows = relation_rows()
    row_tensor = torch.tensor([row for row, _code in rows], dtype=torch.int32)
    block_modules = [
        f"MinModulus.Generated.SHCSixN105A{first:02d}B{offset:02d}"
        for first in range(51)
        for offset, _second in enumerate(range(first + 1, 52))
    ]
    block_index = {module: index for index, module in enumerate(block_modules)}
    first_values = range(51) if only_first is None else (only_first,)
    total_blocks = 0
    total_branches = 0
    for first in first_values:
        blocks = []
        for offset, second in enumerate(range(first + 1, 52)):
            tree, branches = choose_tree(first, second, rows, row_tensor)
            blocks.append((offset, second))
            module = f"MinModulus.Generated.SHCSixN105A{first:02d}B{offset:02d}"
            index = block_index[module]
            predecessor = block_modules[index - BUILD_LANES] if index >= BUILD_LANES else None
            write_generated(
                output / f"SHCSixN105A{first:02d}B{offset:02d}.lean",
                block_source(first, offset, second, tree, predecessor),
            )
            total_blocks += 1
            total_branches += branches
        write_generated(
            output / f"SHCSixN105A{first:02d}.lean",
            shard_source(first, blocks),
        )
    if only_first is None:
        write_generated(output / "SHCSixN105.lean", aggregate_source())
    return len(tuple(first_values)), total_blocks, total_branches


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--first", type=int, choices=range(51))
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "MinModulus" / "Generated",
    )
    args = parser.parse_args()
    shards, blocks, branches = generate(args.output, args.first)
    print(f"N=105: wrote {shards} fixed-first shards, {blocks} blocks, {branches} proof branches")


if __name__ == "__main__":
    main()
