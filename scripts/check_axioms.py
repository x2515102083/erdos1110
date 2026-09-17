"""Fail closed unless every audited endpoint has only standard Lean axioms."""
import re
import sys
from pathlib import Path

EXPECTED = {
    "Erdos1110.yuChenRange_unconditional",
    "Erdos1110.erdos1110_pairwise_unconditional",
    "Erdos1110.primitiveRepresentable_iff",
    "Erdos1110.erdos1110_pairwise",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
    r"does not depend on any axioms)\s*$", re.MULTILINE
)


def check(text):
    reports = {}
    for match in REPORT.finditer(text):
        name, axioms = match.groups()
        if name in reports:
            raise ValueError(f"Duplicate axiom report: {name}")
        reports[name] = {a.strip() for a in (axioms or "").split(",") if a.strip()}
    if set(reports) != EXPECTED:
        raise ValueError(f"Missing/unexpected targets: {set(reports) ^ EXPECTED}")
    for name, axioms in reports.items():
        if axioms - ALLOWED:
            raise ValueError(f"Unexpected axioms for {name}: {axioms - ALLOWED}")


if __name__ == "__main__":
    check(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    print("All four endpoint axiom reports passed; not independent mathematical review.")
