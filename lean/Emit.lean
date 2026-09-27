import VerifiedGarbage.Artifacts

/-!
# The emitter

Renders every entry of `VG.artifacts` into Rust, under `src/asm/` of the
crate (by default `../src/asm`, relative to `lean/`). Run it from `lean/`
after `lake build` (which checks every proof):

* `lake env lean --run Emit.lean [DIR]` writes the files (and deletes stale
  `.rs` files).
* `lake env lean --run Emit.lean --check [DIR]` writes nothing and fails if
  the files on disk differ from what would be generated; CI runs this.

(It is run by the interpreter rather than as a `lean_exe` so that CI does not
have to compile Mathlib to native code.)
-/

def usage : String := "usage: lake env lean --run Emit.lean [--check] [DIR]"

def main (args : List String) : IO UInt32 := do
  let (check, rest) := match args with
    | "--check" :: rest => (true, rest)
    | rest => (false, rest)
  let dir : System.FilePath ← match rest with
    | [] => pure "../src/asm"
    | [d] => pure d
    | _ => do IO.eprintln usage; return 2
  let files := VG.Rust.files VG.artifacts
  let expected := files.map (·.1)
  let mut ok := true
  unless check do IO.FS.createDirAll dir
  for (name, text) in files do
    let path := dir / name
    if let some parent := path.parent then
      unless check do IO.FS.createDirAll parent
    if check then
      let current ← if ← path.pathExists then IO.FS.readFile path else pure ""
      if current != text then
        IO.eprintln s!"{path} is out of date"
        ok := false
    else
      IO.FS.writeFile path text
      IO.println s!"wrote {path}"
  -- Any other `.rs` file under the directory would be unverified code.
  let expectedPaths := expected.map fun n => (dir / n).normalize
  if ← dir.pathExists then
    for path in ← dir.walkDir do
      if path.extension == some "rs" && !expectedPaths.contains path.normalize then
        if check then
          IO.eprintln s!"{path} is not generated from any artifact"
          ok := false
        else
          IO.FS.removeFile path
          IO.println s!"removed stale {path}"
  if !ok then
    IO.eprintln "run `lake build && lake env lean --run Emit.lean` in lean/ and commit the result"
    return 1
  return 0
