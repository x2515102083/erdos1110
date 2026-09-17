import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "check_axioms", Path(__file__).resolve().parents[1] / "scripts/check_axioms.py"
)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AxiomTests(unittest.TestCase):
    def report(self, axioms="propext, Classical.choice, Quot.sound"):
        return "\n".join(f"'{n}' depends on axioms: [{axioms}]" for n in sorted(audit.EXPECTED))

    def test_standard(self):
        audit.check(self.report())

    def test_no_axioms(self):
        audit.check("\n".join(f"'{n}' does not depend on any axioms" for n in audit.EXPECTED))

    def test_multiline(self):
        audit.check(self.report("propext,\n Classical.choice, Quot.sound"))

    def test_forbidden(self):
        for axiom in ("sorryAx", "customAxiom", "Lean.ofReduceBool"):
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                audit.check(self.report(axiom))

    def test_missing(self):
        with self.assertRaises(ValueError):
            audit.check("\n".join(self.report().splitlines()[1:]))

    def test_duplicate(self):
        with self.assertRaises(ValueError):
            audit.check(self.report() + "\n" + self.report())

    def test_empty(self):
        with self.assertRaises(ValueError):
            audit.check("")

    def test_unexpected(self):
        with self.assertRaises(ValueError):
            audit.check(self.report() + "\n'Other.theorem' depends on axioms: []")
