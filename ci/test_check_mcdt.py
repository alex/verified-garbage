"""Regression tests for instruction locations in the MCDT checker."""

import contextlib
import io
import pathlib
import tempfile
import unittest
from unittest.mock import patch

import check_mcdt


class InstructionLocations(unittest.TestCase):
    def test_labels_and_ignored_lines(self):
        body = '\n'.join([
            '    naked_asm!(',
            '        "2:",',
            '',
            '        // ignored comment',
            '        "mov eax, 8127",',
            '        "3:",',
            '        "3:",',
            '',
            '        "pmuludq xmm0, xmm1",',
            '        "2:",',
            '        "ret",',
            '    );',
        ])
        self.assertEqual(
            check_mcdt.code(body, 10),
            (["mov eax, 8127", "pmuludq xmm0, xmm1", "ret"],
             [14, 18, 20], {"2": [0, 2], "3": [1, 1]}),
        )

    def test_diagnostics_across_functions_and_files(self):
        # Include documentation, blank lines, and labels before instructions;
        # main() must reset its file offset and code() must include labels.
        text = '\n'.join([
            '// generated code',
            '',
            'pub(crate) unsafe extern "sysv64" fn vg_first() {',
            '    naked_asm!(',
            '        "2:",',
            '        "pmuludq xmm0, xmm1",',
            '    );',
            '}',
            '',
            '/// second function',
            'pub(crate) unsafe extern "sysv64" fn vg_second() {',
            '',
            '    naked_asm!(',
            '        "pmullw xmm0, xmm1",',
            '    );',
            '}',
        ])
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for arch in check_mcdt.TARGETS:
                path = root / "src" / "asm" / arch / "test.rs"
                path.parent.mkdir(parents=True)
                path.write_text(text)
            stderr = io.StringIO()
            with patch.object(check_mcdt, "ROOT", root), patch.object(
                check_mcdt, "ASM", root / "src" / "asm"
            ), contextlib.redirect_stderr(stderr):
                self.assertEqual(check_mcdt.main(), 1)
        expected = []
        for arch in check_mcdt.TARGETS:
            for name, line, instr in [
                ("vg_first", 6, "pmuludq xmm0, xmm1"),
                ("vg_second", 14, "pmullw xmm0, xmm1"),
            ]:
                expected.append(
                    f"src/asm/{arch}/test.rs ({name}):{line}: `{instr}` is outside "
                    "Intel's MXCSR prologue and epilogue "
                    "(MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"
                )
        self.assertEqual(stderr.getvalue().splitlines(), expected)


if __name__ == "__main__":
    unittest.main()
