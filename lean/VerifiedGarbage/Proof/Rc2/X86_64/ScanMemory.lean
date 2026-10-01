import VerifiedGarbage.Proof.Rc2.X86_64.Lookup

/-! # Existing contract permissions used by vector schedule scans -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64

structure ScanMemory (s : State) : Prop where
  bytes : ∀ i < 128, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1
  vectors : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16
  scratch : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 64) 16

instance (s : State) : CoeFun (ScanMemory s)
    (fun _ => ∀ i, i < 128 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 i) 1) where
  coe := fun h => h.bytes

theorem ScanMemory.keep {s s' : State} {rs : List Reg} (h : ScanMemory s)
    (keep : Keep rs s s') (hk : .rdi ∉ rs) (hs : .rdx ∉ rs) : ScanMemory s' := by
  constructor
  · rw [keep.rd, keep.wr, keep.reg .rdi hk]
    exact h.bytes
  · rw [keep.rd, keep.wr, keep.reg .rdi hk]
    exact h.vectors
  · rw [keep.wr, keep.reg .rdx hs]
    exact h.scratch

end VG.Proof.Rc2.X86_64
