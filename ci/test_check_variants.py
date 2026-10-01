"""Tests for the variant checker's composition of suffixes."""

import unittest

import check_variants

SIG = ("out: *mut u8", "")


def fns(calls):
    """A target's functions, all with one signature, from their callees."""
    return {"x": {name: (SIG, set(callees)) for name, callees in calls.items()}}


class Composition(unittest.TestCase):
    # Two independent dimensions: `h` (with `h_a`) and `f` (with `f_b`),
    # both called by `g`.
    BASE = {
        "vg_h": [], "vg_h_a": [], "vg_f": [], "vg_f_b": [],
        "vg_g": ["vg_h", "vg_f"], "vg_g_a": ["vg_h_a", "vg_f"], "vg_g_b": ["vg_h", "vg_f_b"],
    }
    RUST = "vg_g vg_g_a vg_g_b"

    def test_either_order(self):
        for name in ("vg_g_a_b", "vg_g_b_a"):
            with self.subTest(name=name):
                calls = dict(self.BASE, **{name: ["vg_h_a", "vg_f_b"]})
                self.assertEqual(check_variants.check(fns(calls), self.RUST + " " + name), [])

    def test_missing_composition(self):
        errors = check_variants.check(fns(self.BASE), self.RUST)
        self.assertEqual(len(errors), 2)
        self.assertIn("vg_g_a calls vg_f, which has the variant vg_f_b, but there is no vg_g_a_b",
                      errors[0])
        self.assertIn("vg_g_b calls vg_h, which has the variant vg_h_a, but there is no vg_g_b_a",
                      errors[1])

    def test_composition_must_call_both(self):
        calls = dict(self.BASE, vg_g_a_b=["vg_h_a", "vg_f"])
        errors = check_variants.check(fns(calls), self.RUST + " vg_g_a_b")
        self.assertEqual(errors, ["x: vg_g_a_b does not call vg_f_b"])


if __name__ == "__main__":
    unittest.main()
