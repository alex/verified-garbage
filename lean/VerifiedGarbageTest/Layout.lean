import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.Rust

/-!
# Golden tests for the documented obligations of signatures

`Sig.layoutDoc` and `Sig.layoutNote` write, into every function's `# Safety`
section, what `Sig.contract` requires of where its buffers are, which depends
on the target's calling convention (`Abi.argAreaDoc`, `Abi.reservedDoc`) and
on the stack the function uses. These tests pin down the text on each target.
-/

namespace VG.Test.Layout

/-- Two writable buffers, two read-only ones and an integer. -/
def sample : Sig where
  params := [("w", .array true .u8 16), ("r", .slice false .u8 "len"), ("n", .int .u32 true),
      ("x", .array true .u64 4), ("y", .array false .u32 2)]

/-- One writable buffer. -/
def one : Sig where
  params := [("state", .array true .u8 64), ("n", .int .u64 true)]

/-- Read-only buffers only. -/
def ro : Sig where
  params := [("a", .array false .u8 16), ("b", .array false .u8 16)]

/-- No buffers. -/
def none' : Sig where
  params := [("a", .int .u64 false)]

#guard Sig.layoutDoc X86_64.abi sample false 0 == [
    "`w` and `x` must not overlap each other, `r` or `y` (distinct Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may overlap the return address on the stack, or wrap around \
      the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc X86_64.abi sample true 8 == [
    "`w` and `x` must not overlap each other, `r` or `y` (distinct Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may overlap the return address on the stack or the 8 bytes of \
      stack below it, or wrap around the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc AArch64.abi sample false 0 == [
    "`w` and `x` must not overlap each other, `r` or `y` (distinct Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may wrap around the end of the address space (no Rust object \
      does)."]

#guard Sig.layoutDoc AArch64.abi sample true 16 == [
    "`w` and `x` must not overlap each other, `r` or `y` (distinct Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may overlap the 16 bytes of stack below the stack pointer, or \
      wrap around the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc Arm.abi sample false 0 == [
    "`w` and `x` must not overlap each other, `r`, `y` or the arguments on the stack (distinct \
      Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may wrap around the end of the address space (no Rust object \
      does)."]

#guard Sig.layoutDoc Arm.abi sample true 8 == [
    "`w` and `x` must not overlap each other, `r`, `y` or the arguments on the stack (distinct \
      Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may overlap the 8 bytes of stack below the stack pointer, or \
      wrap around the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc X86.abi sample false 0 == [
    "`w` and `x` must not overlap each other, `r`, `y` or the arguments on the stack (distinct \
      Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may overlap the return address on the stack, or wrap around \
      the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc X86.abi sample true 4 == [
    "`w` and `x` must not overlap each other, `r` or `y` (distinct Rust objects never do).",
    "None of `w`, `r`, `x` and `y` may overlap the arguments on the stack, overlap the return \
      address on the stack or the 4 bytes of stack below it, or wrap around the end of the address \
      space (no Rust object does)."]

#guard Sig.layoutDoc X86_64.abi one false 0 == [
    "`state` must not overlap the return address on the stack, or wrap around the end of the \
      address space (no Rust object does)."]

#guard Sig.layoutDoc Arm.abi one false 0 == [
    "`state` must not wrap around the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc X86.abi one true 0 == [
    "`state` must not overlap the arguments on the stack, overlap the return address on the \
      stack, or wrap around the end of the address space (no Rust object does)."]

#guard Sig.layoutDoc X86_64.abi ro false 0 == [
    "Neither `a` nor `b` may overlap the return address on the stack, or wrap around the end of \
      the address space (no Rust object does)."]

#guard Sig.layoutDoc X86_64.abi none' false 0 == []

#guard Sig.layoutNote X86.abi sample true ==
  ["The function may overwrite the arguments on the stack, as the calling convention lets it."]

#guard Sig.layoutNote X86.abi sample false == []

#guard Sig.layoutNote Arm.abi sample true == []

#guard Sig.layoutNote X86_64.abi sample true == []

/-! ## Rendering: the note goes before `# Safety` -/

def safeDoc : String := "Does things.\n\n# Safety\n\n* `p` must be valid."

#guard Rust.insertNotes safeDoc [] == safeDoc
#guard Rust.insertNotes safeDoc ["A note."] ==
  "Does things.\n\nA note.\n\n# Safety\n\n* `p` must be valid."
#guard Rust.insertNotes "No safety section." ["A note."] == "No safety section."

end VG.Test.Layout
