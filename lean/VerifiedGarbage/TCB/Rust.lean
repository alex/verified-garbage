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

A call (`Code.call name body`) is a call instruction whose operand is the
symbol of the Rust function `name` (a `sym` operand). The model runs `body`
for it, so `files` checks that `name` is an artifact of the same target
whose printed code is exactly that of `body`, for every call, including the
calls in `body` itself; otherwise nothing is emitted.
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

/-- The distinct values of `as`, in first-seen order. -/
def dedup (as : List String) : List String :=
  as.foldl (init := []) fun acc a => if acc.contains a then acc else acc ++ [a]

/-- One line of the `naked_asm!` template: a call names its function as the
operand of the same name. -/
def line (call : String) : Line → String
  | .text l => s!"        \"{escape l}\",\n"
  | .call n => s!"        \"{escape call} " ++ "{" ++ n ++ "}\",\n"

/-- One artifact as a Rust naked function; `moduleOf` gives the module of
each function it calls. -/
def function (a : Artifact) (moduleOf : String → String) : String :=
  let body := a.target.printer.function a.code
  let callees := dedup (body.filterMap fun | .call n => some n | .text _ => none)
  docComment "" a.doc ++
  "#[unsafe(naked)]\n" ++
  s!"pub(crate) unsafe extern \"{a.target.rustAbi}\" fn {a.name}{a.sig.rust} " ++ "{\n" ++
  "    core::arch::naked_asm!(\n" ++
  String.join (body.map (line a.target.printer.call)) ++
  String.join (callees.map fun n => s!"        {n} = sym super::{moduleOf n}::{n},\n") ++
  "    )\n" ++
  "}\n"

/-- The distinct values of `f` over `as`, in first-seen order. -/
def distinct (as : List Artifact) (f : Artifact → String) : List String :=
  dedup (as.map f)

/-- The artifact that a call of `name` in `a` calls. -/
def callee (as : List Artifact) (a : Artifact) (name : String) : Option Artifact :=
  as.find? fun b => b.target.name == a.target.name && b.name == name

/-- Every call in the code of `a`, and in the code of the functions it calls,
is of an artifact of the same target whose printed code is that of the
called code. -/
def checkCalls (as : List Artifact) (a : Artifact) : Except String Unit :=
  a.code.calls.forM fun (n, body) =>
    match callee as a n with
    | none => throw s!"{a.target.name}: {a.name} calls {n}, which is not an artifact"
    | some b =>
      unless a.target.printer.function body == b.target.printer.function b.code do
        throw s!"{a.target.name}: {a.name} calls {n}, whose code is not what the call runs"

/-- `mod` declarations for generated child modules (never reformatted by rustfmt). -/
def modDecls (ms : List String) (cfg : String → Option String) : String :=
  String.join (ms.map fun m =>
    let c := match cfg m with
      | some c => s!"#[cfg({c})]\n"
      | none => ""
    s!"\n{c}#[rustfmt::skip]\npub(crate) mod {m};\n")

/-- The generated files, given the module of each function each artifact calls. -/
def render (as : List Artifact) (moduleOf : Artifact → String → String) : List (String × String) :=
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
        String.join ((arts.filter (·.module == m)).map fun a => "\n" ++ function a (moduleOf a)))
  ("mod.rs", root) :: (targets.map perTarget).flatten

/-- The generated files, as paths relative to `src/asm/` and their contents:
`mod.rs`, and for each target `<target>/mod.rs` and one `<target>/<module>.rs`
per module; an error if a call is not of the code it runs (`checkCalls`). -/
def files (as : List Artifact) : Except String (List (String × String)) := do
  as.forM (checkCalls as)
  return render as fun a n => ((callee as a n).map (·.module)).getD ""

end VG.Rust
