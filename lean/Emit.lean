import VerifiedGarbage.TCB.Emit

/-!
# The emitter

Renders every artifact (those of `VerifiedGarbage/Artifacts.lean`, of
each registration file under `VerifiedGarbage/Artifacts/`, and of each
generic file under `VerifiedGarbage/Generic/` for each variant under
`VerifiedGarbage/Variants/`, see `VerifiedGarbage/TCB/Emit.lean`) into Rust, under `src/asm/` of the crate
(by default `../src/asm`, relative to `lean/`). Run it from `lean/` after
`lake build` (which checks every proof):

* `lake env lean --run Emit.lean [DIR]` writes the files (and deletes stale
  `.rs` files).
* `lake env lean --run Emit.lean --check [DIR]` writes nothing and fails if
  the files on disk differ from what would be generated; CI runs this.

It writes a program that imports every registration file
(`.lake/emit/Driver.lean`) and runs it with the same arguments. (It is run
by the interpreter rather than as a `lean_exe` so that CI does not have to
compile Mathlib to native code.) The interpreter runs the trusted base, which
does the printing and checking, as the compiled code of the `NativeTCB`
library (`lakefile.toml`), which `lake build` builds, and so an order of
magnitude faster.
-/

/-- The shared library of `NativeTCB`, as Lake names it. -/
def nativeTCB : System.FilePath :=
  ".lake" / "build" / "lib" /
    if System.Platform.isWindows then "VerifiedGarbage_NativeTCB.dll"
    else s!"libVerifiedGarbage_NativeTCB.{if System.Platform.isOSX then "dylib" else "so"}"

def main (args : List String) : IO UInt32 := do
  unless ← nativeTCB.pathExists do
    IO.eprintln s!"{nativeTCB} is missing: run `lake build` first"
    return 1
  let driver : System.FilePath := ".lake" / "emit" / "Driver.lean"
  IO.FS.createDirAll ".lake/emit"
  IO.FS.writeFile driver (VG.Emit.driver (← VG.Emit.registrations)
    (← VG.Emit.grouped VG.Emit.genericDir) (← VG.Emit.grouped VG.Emit.variantDir))
  let lean ← IO.appPath
  let child ← IO.Process.spawn
    { cmd := lean.toString,
      args := #[s!"--load-dynlib={nativeTCB}", "--run", driver.toString] ++ args.toArray }
  child.wait
