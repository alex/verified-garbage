import VerifiedGarbage.TCB.Emit

/-!
# The emitter

Renders every artifact (those of `VerifiedGarbage/Artifacts.lean` and of
each registration file under `VerifiedGarbage/Artifacts/`, see
`VerifiedGarbage/TCB/Emit.lean`) into Rust, under `src/asm/` of the crate
(by default `../src/asm`, relative to `lean/`). Run it from `lean/` after
`lake build` (which checks every proof):

* `lake env lean --run Emit.lean [DIR]` writes the files (and deletes stale
  `.rs` files).
* `lake env lean --run Emit.lean --check [DIR]` writes nothing and fails if
  the files on disk differ from what would be generated; CI runs this.

It writes a program that imports every registration file
(`.lake/emit/Driver.lean`) and runs it with the same arguments. (It is run
by the interpreter rather than as a `lean_exe` so that CI does not have to
compile Mathlib to native code.)
-/

def main (args : List String) : IO UInt32 := do
  let driver : System.FilePath := ".lake" / "emit" / "Driver.lean"
  IO.FS.createDirAll ".lake/emit"
  IO.FS.writeFile driver (VG.Emit.driver (← VG.Emit.registrations))
  let lean ← IO.appPath
  let child ← IO.Process.spawn
    { cmd := lean.toString, args := #["--run", driver.toString] ++ args.toArray }
  child.wait
