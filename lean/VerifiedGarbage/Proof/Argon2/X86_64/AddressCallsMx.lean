import VerifiedGarbage.Proof.Argon2.X86_64.AddressCalls

/-! The baseline independent-address calls preserve all MXCSR bits. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

theorem compression_noMx : VG.Impl.Argon2.X86_64.compress.allInstrs (fun i => !loadsMxcsr i) = true :=
  by lit_decide

theorem stage_noMx (x y out : Nat) : (stage x y out).allInstrs (fun i => !loadsMxcsr i) = true := by
  change ((Code.block (args x y out) : Prog isa).allInstrs (fun i => !loadsMxcsr i) &&
    VG.Impl.Argon2.X86_64.compress.allInstrs (fun i => !loadsMxcsr i)) = true
  rw [compression_noMx]
  rfl

theorem calls_noMx : calls.allInstrs (fun i => !loadsMxcsr i) = true := by
  change ((stage 7168 5120 4096).allInstrs (fun i => !loadsMxcsr i) &&
    (stage 7168 4096 6144).allInstrs (fun i => !loadsMxcsr i)) = true
  rw [stage_noMx, stage_noMx]
  rfl

theorem calls_mx_ok (p : Spec.Argon2.Params) (pass lane slice counter : Nat) (s : State) (h : Ready s)
    (zero : Spec.Argon2.blockAt s.mem (off (work s) 7168) = Spec.Argon2.zeroBlock)
    (input : Spec.Argon2.blockAt s.mem (off (work s) 5120) =
      Proof.Argon2.addressInput p pass lane slice counter) :
    WP isa calls s fun t => Generated s t p pass lane slice counter ∧ t.mxcsr = s.mxcsr :=
  WP.mono_mx calls_noMx (calls_ok p pass lane slice counter s h zero input)
    (fun _ generated mx => ⟨generated, mx⟩)

end VG.Proof.Argon2.X86_64.AddressCalls
