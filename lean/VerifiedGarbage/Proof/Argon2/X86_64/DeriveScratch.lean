import VerifiedGarbage.Proof.Argon2.X86_64.DeriveStore

/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rbp + 248) 64
  regs : ∀ r, r ≠ .rbx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 248) 8) :
    WP isa (.block [.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))]) s (ScratchLoaded s) := by
  have ea : s.ea (Impl.Argon2.X86_64.at_ .rbp 248) = s.gpr .rbp + 248 := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea, read,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact RegUpd.gpr_setReg_self ..
  · intro r hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

end VG.Proof.Argon2.X86_64.Derive
