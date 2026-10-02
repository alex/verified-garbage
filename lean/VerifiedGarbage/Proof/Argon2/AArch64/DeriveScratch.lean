import VerifiedGarbage.Proof.Argon2.AArch64.DeriveStore

/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  regs : ∀ r, r ≠ .x24 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8) :
    WP isa (.block [.ldr .x .x24 .x19 248]) s (ScratchLoaded s) := by
  refine (Instructions.load_ok s .x24 .x19 248 (by decide) (by decide) read).mono ?_
  rintro t ⟨value, kept⟩
  refine ⟨value, ?_, kept.mem, kept.rd, kept.wr, kept.sp⟩
  intro r hr
  exact kept.regs r (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Argon2.AArch64.Derive
