import VerifiedGarbage.TCB.Artifact

/-!
# Rendering artifacts as Rust

**Trusted.** Every artifact becomes a Rust naked function whose entire body
is the printed assembly:

```rust
#[unsafe(naked)]
pub(crate) unsafe extern "<abi>" fn <name><sig> {
    core::arch::naked_asm!(
        "<line>",
        …
    )
}
```

A naked function has no compiler-generated prologue or epilogue, so the
machine code that runs is exactly the code that was verified (plus the
final `ret` from the printer). The functions of each target are collected
in one module, `src/asm/<target>.rs`, compiled only under the target's
`cfg`.
-/

namespace VG.Rust

/-- Escape a string for a Rust string literal that is also an `asm!`
template: `{`/`}` are template placeholders and must be doubled. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '{' => acc ++ "{{"
    | '}' => acc ++ "}}"
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | '\n' => acc ++ "\\n"
    | c => acc.push c

def header : String :=
  "// @generated from lean/VerifiedGarbage/Artifacts.lean by lean/Emit.lean. DO NOT EDIT.\n"

def docComment (indent doc : String) : String :=
  String.join ((doc.splitOn "\n").map fun l =>
    if l.isEmpty then s!"{indent}///\n" else s!"{indent}/// {l}\n")

/-- One artifact as a Rust naked function. -/
def function (a : Artifact) : String :=
  let body := a.target.printer.function a.name a.code
  docComment "" a.doc ++
  "#[unsafe(naked)]\n" ++
  s!"pub(crate) unsafe extern \"{a.target.rustAbi}\" fn {a.name}{a.rustSig} " ++ "{\n" ++
  "    core::arch::naked_asm!(\n" ++
  String.join (body.map fun l => s!"        \"{escape l}\",\n") ++
  "    )\n" ++
  "}\n"

/-- The target names that have at least one artifact, in first-seen order. -/
def targetNames (as : List Artifact) : List String :=
  as.foldl (init := []) fun acc a =>
    if acc.contains a.target.name then acc else acc ++ [a.target.name]

/-- The generated files, as paths relative to `src/asm/` and their contents. -/
def files (as : List Artifact) : List (String × String) :=
  let names := targetNames as
  let modFor (n : String) : String × String :=
    let arts := as.filter (·.target.name == n)
    (s!"{n}.rs",
      header ++ s!"//! Verified functions for `{n}`.\n" ++
      String.join (arts.map fun a => "\n" ++ function a))
  let cfgOf (n : String) : String :=
    match as.find? (·.target.name == n) with
    | some a => a.target.rustCfg
    | none => "any()"
  let modRs :=
    header ++
    "//! Formally verified assembly, emitted from Lean. See `lean/README.md`.\n" ++
    "//!\n" ++
    "//! Every function in these modules is the direct rendering of an `Artifact`\n" ++
    "//! whose machine code has been proven correct, memory safe and constant time\n" ++
    "//! against its contract.\n" ++
    String.join (names.map fun n =>
      s!"\n#[cfg({cfgOf n})]\n#[allow(dead_code)]\n#[rustfmt::skip]\npub(crate) mod {n};\n")
  ("mod.rs", modRs) :: names.map modFor

end VG.Rust
