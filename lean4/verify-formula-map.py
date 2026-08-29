#!/usr/bin/env python3
"""Fail-closed coverage check for the manuscript-to-Lean theorem map."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
TEX = ROOT / "paper" / "fibonacci_ribbon_tableaux_enumeration.tex"
HUMAN_MAP = ROOT / "FORMULA_MAP.md"
LEAN_MAP = ROOT / "lean4" / "FibonacciRibbonKernel" / "ManuscriptFormulaMap.lean"


def main() -> None:
    tex = TEX.read_text(encoding="utf-8")
    labels = re.findall(r"\\label\{([^}]+)\}", tex)
    if not labels:
        raise RuntimeError("manuscript has no labels")
    duplicates = sorted({label for label in labels if labels.count(label) > 1})
    if duplicates:
        raise RuntimeError(f"duplicate manuscript labels: {duplicates}")

    human = HUMAN_MAP.read_text(encoding="utf-8")
    lean = LEAN_MAP.read_text(encoding="utf-8")
    missing_human = [label for label in labels if f"`{label}`" not in human]
    missing_lean = [label for label in labels if label not in lean]
    if missing_human:
        raise RuntimeError(f"FORMULA_MAP.md misses labels: {missing_human}")
    if missing_lean:
        raise RuntimeError(f"ManuscriptFormulaMap.lean misses labels: {missing_lean}")

    print(f"fibonacci_ribbon_formula_map=passed labels={len(labels)}")


if __name__ == "__main__":
    main()
