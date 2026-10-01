import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Semantics

/-! Stack consumption in 16-byte units, including contiguous allocations. -/
namespace VG

def AArch64.Instr.frameUnits : AArch64.Instr → Nat
  | .alloc bytes => bytes / 16
  | _ => 1

/-- Maximum simultaneous stack consumption in 16-byte units. For ordinary
register-save frames this is the usual frame depth. -/
def Code.aarch64Depth : Prog AArch64.isa → Nat
  | .block _ => 0
  | .seq a b => max a.aarch64Depth b.aarch64Depth
  | .ite _ t e => max t.aarch64Depth e.aarch64Depth
  | .loop b _ => b.aarch64Depth
  | .call _ b => b.aarch64Depth
  | .frame i b _ => b.aarch64Depth + i.frameUnits

end VG
