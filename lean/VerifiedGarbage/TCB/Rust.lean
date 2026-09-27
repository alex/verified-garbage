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
in `src/asm/<target>/`, one file per `module`, compiled only under the
target's `cfg`.
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
  let body := a.target.printer.function a.code
  docComment "" a.doc ++
  "#[unsafe(naked)]\n" ++
  s!"pub(crate) unsafe extern \"{a.target.rustAbi}\" fn {a.name}{a.rustSig} " ++ "{\n" ++
  "    core::arch::naked_asm!(\n" ++
  String.join (body.map fun l => s!"        \"{escape l}\",\n") ++
  "    )\n" ++
  "}\n"

/-- The distinct values of `f` over `as`, in first-seen order. -/
def distinct (as : List Artifact) (f : Artifact → String) : List String :=
  as.foldl (init := []) fun acc a => if acc.contains (f a) then acc else acc ++ [f a]

/-- `mod` declarations for generated child modules (never reformatted by rustfmt). -/
def modDecls (ms : List String) (cfg : String → Option String) : String :=
  String.join (ms.map fun m =>
    let c := match cfg m with
      | some c => s!"#[cfg({c})]\n"
      | none => ""
    s!"\n{c}#[rustfmt::skip]\npub(crate) mod {m};\n")

/-- The generated files, as paths relative to `src/asm/` and their contents:
`mod.rs`, and for each target `<target>/mod.rs` and one `<target>/<module>.rs`
per module. -/
def files (as : List Artifact) : List (String × String) :=
  let targets := distinct as (·.target.name)
  let cfgOf (t : String) : Option String := (as.find? (·.target.name == t)).map (·.target.rustCfg)
  let root :=
    header ++
    "//! Formally verified assembly, emitted from Lean. See `lean/README.md`.\n" ++
    "//!\n" ++
    "//! Every function in these modules is the direct rendering of an `Artifact`\n" ++
    "//! whose machine code has been proven correct, memory safe and constant time\n" ++
    "//! against its contract.\n" ++
    modDecls targets cfgOf
  let perTarget (t : String) : List (String × String) :=
    let arts := as.filter (·.target.name == t)
    let modules := distinct arts (·.module)
    (s!"{t}/mod.rs", header ++ s!"//! Verified functions for `{t}`.\n" ++
      modDecls modules (fun _ => none)) ::
    modules.map fun m =>
      (s!"{t}/{m}.rs",
        header ++ s!"//! Verified `{m}` functions for `{t}`.\n" ++
        "#![allow(dead_code)]\n" ++
        String.join ((arts.filter (·.module == m)).map fun a => "\n" ++ function a))
  ("mod.rs", root) :: (targets.map perTarget).flatten

end VG.Rust
