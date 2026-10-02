import VerifiedGarbage.Proof.Argon2.AArch64.DeriveLit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.AArch64.InitialLit
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.AArch64.ParametersLit

/-! The complete derivation preserves SIMD registers for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

local notation "property" => keepsV

theorem initial_preservedV (v : HPrime.Backend) :
    (Impl.Argon2.AArch64.Initial.code v.hash).allInstrs property = true := by
  have init : v.hash.init.allInstrs property = true := v.initV
  have update : v.hash.update.allInstrs property = true := v.updateV
  have finalize : v.hash.finalize.allInstrs property = true := v.finalizeV
  simp only [Impl.Argon2.AArch64.Initial.code, Impl.Argon2.AArch64.Initial.start,
    Impl.Argon2.AArch64.Initial.absorb, Impl.Argon2.AArch64.Initial.finish,
    Impl.Argon2.AArch64.HPrime.init, Impl.Argon2.AArch64.HPrime.absorbFixed,
    Impl.Argon2.AArch64.HPrime.update, Impl.Argon2.AArch64.HPrime.finalize, Code.allInstrs]
  rw [init, update, finalize]
  lit_decide

theorem memory_preservedV (v : HPrime.Backend) (name : String) :
    (Impl.Argon2.AArch64.MemoryInit.code name v.hash).allInstrs property = true := by
  simp only [Impl.Argon2.AArch64.MemoryInit.code, Impl.Argon2.AArch64.MemoryInit.clear,
    Impl.Argon2.AArch64.MemoryInit.lane, Impl.Argon2.AArch64.MemoryInit.block, Code.allInstrs]
  rw [HPrime.code_keepsV v]
  lit_decide

theorem frame_preservedV (body : Prog isa) (rs : List Reg) (h : body.allInstrs property = true) :
    (Impl.Argon2.AArch64.Derive.frame body rs).allInstrs property = true := by
  induction rs with
  | nil => simpa [Impl.Argon2.AArch64.Derive.frame, Code.allInstrs, keepsV, vdstOf] using h
  | cons r rs ih => simpa [Impl.Argon2.AArch64.Derive.frame, Code.allInstrs, keepsV, vdstOf] using ih

theorem code_preservedV (v : HPrime.Backend) (name : String) :
    (Impl.Argon2.AArch64.Derive.code name v.hash).allInstrs property = true := by
  unfold Impl.Argon2.AArch64.Derive.code
  apply frame_preservedV
  simp only [Impl.Argon2.AArch64.Derive.body, Impl.Argon2.AArch64.InitialBody.code,
    Impl.Argon2.AArch64.InitFill.code, Impl.Argon2.AArch64.FillFinish.code,
    Impl.Argon2.AArch64.Finish.code, Impl.Argon2.AArch64.FinalOutput.code, Code.allInstrs]
  rw [initial_preservedV v, memory_preservedV v name, HPrime.code_keepsV v]
  lit_decide

end VG.Proof.Argon2.AArch64.Derive
