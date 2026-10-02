import VerifiedGarbage.Proof.X448.X86.Normalize

/-!
# X448 on x86 (32-bit): field operations and their frame
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps clob s t
  mem : FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base) :
    Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 112 ≤ ACC


end VG.Proof.X448.X86
