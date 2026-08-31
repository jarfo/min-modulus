#!/usr/bin/env python3
"""Generate kernel-checked normalized six-coordinate SHC certificates.

The distinguished coordinate is 1.  The other five values are an increasing
selection from 2 through N - 1.  For each fixed pair of initial tail values,
Torch finds a decision tree of subset-collision/head-2 witnesses.  Symbolic
branches use only relations independent of the remaining coordinates; the
emitted Lean files check every relation with ordinary kernel reduction.
Generated block imports form two dependency lanes so fresh Lake builds never
compile more than two certificate blocks concurrently.  This script and
Torch remain outside the trusted base.
"""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

import torch


COORDINATES = 6
BUILD_LANES = 2


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
    modulus: int,
    tail_values: list[int],
    first: int,
    second: int,
    rows: list[tuple[tuple[int, ...], int]],
    row_tensor: torch.Tensor,
) -> tuple[list[tuple[int | None, list[tuple[int | None, list[int]]]]], int]:
    tails = list(itertools.combinations(range(second + 1, len(tail_values)), 3))
    candidates = torch.tensor(
        [
            (1, tail_values[first], tail_values[second], *(tail_values[i] for i in rest))
            for rest in tails
        ],
        dtype=torch.int32,
    )
    hits = torch.remainder(candidates @ row_tensor.T, modulus) == 0
    remaining = len(tail_values) - second - 1
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
                    raise RuntimeError(
                        f"uncovered block ({first}, {second}) at N={modulus}: {bad}"
                    )
                leaf_codes.append(rows[int(torch.argmax(matching.to(torch.int8)))][1])
            by_d.append((None, leaf_codes))
            branches += len(leaf_codes)
        tree.append((None, by_d))
    return tree, branches


def module_name(modulus: int, first: int, offset: int) -> str:
    return f"MinModulus.Generated.SHCSixNormalizedN{modulus}A{first:02d}B{offset:02d}"


def block_source(
    modulus: int,
    tail_count: int,
    first: int,
    offset: int,
    second: int,
    tree: list[tuple[int | None, list[tuple[int | None, list[int]]]]],
    predecessor: str | None,
) -> str:
    suffix = f"{first:02d}_{offset:02d}"
    remaining = tail_count - second - 1
    first_value = first + 2
    second_value = second + 2
    lines = [
        f"import {predecessor or 'MinModulus.SHCSixCertificate'}\n\n",
        "namespace MinModulus.SHCSixCertificate.Generated\n\n",
        "set_option maxRecDepth 1000000\n",
        "set_option maxHeartbeats 1000000000\n\n",
    ]
    for third, (code_c, by_d) in enumerate(tree):
        tail_type = (
            f"Σ d : Fin ({remaining} - {third} - 2), "
            f"Fin ({remaining} - ({third} + 1 + d.val) - 1)"
        )
        theorem = f"certificate{modulus}_a{first:02d}_b{offset:02d}_c{third:02d}"
        lines.extend(
            [
                f"private theorem {theorem} (q : {tail_type}) : ∃ code,\n",
                "    validRelationCode code ∧\n",
                f"    relationZeroNat {modulus} (blockValues {first_value} {second_value} "
                f"⟨(⟨{third}, by norm_num⟩ : Fin ({remaining} - 2)), q⟩) "
                "code = true := by\n",
            ]
        )
        if code_c is not None:
            lines.append(
                f"  exact ⟨{code_c}, by decide, by simp +decide "
                "[relationZeroNat, blockValues, maskSumNat]⟩\n\n"
            )
            continue
        lines.extend(["  rcases q with ⟨d, e⟩\n", "  fin_cases d\n"])
        for code_d, leaf_codes in by_d:
            if code_d is not None:
                lines.append(
                    f"  · exact ⟨{code_d}, by decide, by simp +decide "
                    "[relationZeroNat, blockValues, maskSumNat]⟩\n"
                )
                continue
            lines.append("  · fin_cases e\n")
            for code in leaf_codes:
                lines.append(f"    · exact ⟨{code}, by decide, by decide⟩\n")
        lines.append("\n")
    lines.extend(
        [
            f"theorem certificate{modulus}_a{first:02d}_b{offset:02d} "
            f"(q : IncreasingThree {remaining}) : ∃ code,\n",
            "    validRelationCode code ∧\n",
            f"    relationZeroNat {modulus} (blockValues {first_value} {second_value} q) "
            "code = true := by\n",
            "  rcases q with ⟨c, q⟩\n",
            "  fin_cases c\n",
        ]
    )
    for third in range(remaining - 2):
        lines.append(
            f"  · exact certificate{modulus}_a{first:02d}_b{offset:02d}_c{third:02d} q\n"
        )
    lines.append("\nend MinModulus.SHCSixCertificate.Generated\n")
    return "".join(lines)


def shard_source(
    modulus: int, tail_count: int, first: int, blocks: list[tuple[int, int]]
) -> str:
    imports = "".join(
        f"import {module_name(modulus, first, offset)}\n" for offset, _second in blocks
    )
    first_bound = modulus - 6
    first_value = first + 2
    lines = [
        imports,
        "\nnamespace MinModulus.SHCSixCertificate.Generated\n\n",
        "set_option maxRecDepth 1000000\n",
        "set_option maxHeartbeats 1000000000\n\n",
        f"theorem certificate{modulus}_a{first:02d}\n",
        f"    (q : IncreasingFiveTail {modulus - 2} "
        f"(⟨{first}, by norm_num⟩ : Fin {first_bound})) : ∃ code,\n",
        "      validRelationCode code ∧\n",
        f"      relationZeroNat {modulus} (increasingFiveValues "
        f"(N := {modulus}) ⟨(⟨{first}, by norm_num⟩ : Fin {first_bound}), q⟩) "
        "code = true := by\n",
        "  rcases q with ⟨b, c, d, e⟩\n",
        "  fin_cases b\n",
    ]
    for offset, second in blocks:
        remaining = tail_count - second - 1
        second_value = second + 2
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
                f"    have hv : increasingFiveValues (N := {modulus}) "
                f"⟨(⟨{first}, by norm_num⟩ : Fin {first_bound}), "
                f"⟨⟨{offset}, by norm_num⟩, c, d, e⟩⟩ =\n",
                f"        blockValues {first_value} {second_value} q' := by\n",
                "      funext i\n",
                "      fin_cases i <;> simp [increasingFiveValues, blockValues, q', c', d', e'] "
                "<;> omega\n",
                "    rw [hv]\n",
                f"    exact certificate{modulus}_a{first:02d}_b{offset:02d} q'\n",
            ]
        )
    lines.append("\nend MinModulus.SHCSixCertificate.Generated\n")
    return "".join(lines)


def aggregate_source(modulus: int) -> str:
    first_count = modulus - 6
    imports = "".join(
        f"import MinModulus.Generated.SHCSixNormalizedN{modulus}A{first:02d}\n"
        for first in range(first_count)
    )
    lines = [
        imports,
        "\nnamespace MinModulus.SHCSixCertificate.Generated\n\n",
        f"theorem certificate{modulus} : Certificate {modulus} := by\n",
        "  intro q\n",
        "  rcases q with ⟨a, tail⟩\n",
        "  fin_cases a\n",
    ]
    for first in range(first_count):
        lines.append(f"  · exact certificate{modulus}_a{first:02d} tail\n")
    lines.append("\nend MinModulus.SHCSixCertificate.Generated\n")
    return "".join(lines)


def generate(
    modulus: int, output: Path, only_first: int | None = None
) -> tuple[int, int, int]:
    if modulus < 67 or modulus % 2 == 0:
        raise ValueError("modulus must be odd and at least 67")
    tail_values = list(range(2, modulus))
    tail_count = len(tail_values)
    first_count = tail_count - 4
    if only_first is not None and only_first not in range(first_count):
        raise ValueError(f"first must lie in 0..{first_count - 1}")
    output.mkdir(parents=True, exist_ok=True)
    rows = relation_rows()
    row_tensor = torch.tensor([row for row, _code in rows], dtype=torch.int32)
    block_modules = [
        module_name(modulus, first, offset)
        for first in range(first_count)
        for offset, _second in enumerate(range(first + 1, tail_count - 3))
    ]
    block_index = {module: index for index, module in enumerate(block_modules)}
    first_values = range(first_count) if only_first is None else (only_first,)
    total_blocks = 0
    total_branches = 0
    for first in first_values:
        blocks = []
        for offset, second in enumerate(range(first + 1, tail_count - 3)):
            tree, branches = choose_tree(
                modulus, tail_values, first, second, rows, row_tensor
            )
            blocks.append((offset, second))
            module = module_name(modulus, first, offset)
            index = block_index[module]
            predecessor = block_modules[index - BUILD_LANES] if index >= BUILD_LANES else None
            write_generated(
                output / f"SHCSixNormalizedN{modulus}A{first:02d}B{offset:02d}.lean",
                block_source(
                    modulus,
                    tail_count,
                    first,
                    offset,
                    second,
                    tree,
                    predecessor,
                ),
            )
            total_blocks += 1
            total_branches += branches
        write_generated(
            output / f"SHCSixNormalizedN{modulus}A{first:02d}.lean",
            shard_source(modulus, tail_count, first, blocks),
        )
    if only_first is None:
        write_generated(
            output / f"SHCSixNormalizedN{modulus}.lean", aggregate_source(modulus)
        )
    return len(tuple(first_values)), total_blocks, total_branches


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--modulus", type=int, required=True)
    parser.add_argument("--first", type=int)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "MinModulus" / "Generated",
    )
    args = parser.parse_args()
    shards, blocks, branches = generate(args.modulus, args.output, args.first)
    candidate_count = math.comb(args.modulus - 2, 5)
    print(
        f"N={args.modulus}: wrote {shards} fixed-first shards, {blocks} blocks, "
        f"{branches} proof branches covering {candidate_count} normalized tails"
    )


if __name__ == "__main__":
    main()
