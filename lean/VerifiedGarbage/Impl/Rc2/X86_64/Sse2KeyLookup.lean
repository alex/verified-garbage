import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup

/-! # Eight-way constant-time RC2 schedule scans on baseline x86-64 -/

namespace VG.Impl.Rc2.X86_64.Sse2

open VG.X86_64 VG.Impl.Rc2.X86_64

def keyStep (n : Nat) : List Instr :=
  [.movdquLoad .xmm4 (memOp .rdi (16 * n))] ++ select

def keyLookup : List Instr :=
  start .rdx 63 ++ (List.range 8).flatMap keyStep ++ finish .rdx

end VG.Impl.Rc2.X86_64.Sse2
