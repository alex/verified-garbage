import VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.X86_64.ParametersLit

/-! The complete derivation preserves MXCSR for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

local notation "property" => (fun i => !loadsMxcsr i)

theorem initial_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (Impl.Argon2.X86_64.Initial.code (HPrime.hash v)).allInstrs property = true := by
  have init : (HPrime.hash v).init.allInstrs property = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (HPrime.hash v).update.allInstrs property = true := v.updateMxcsr
  have finalize : (HPrime.hash v).finalize.allInstrs property = true := v.finalizeMxcsr
  simp only [Impl.Argon2.X86_64.Initial.code, Impl.Argon2.X86_64.Initial.start,
    Impl.Argon2.X86_64.Initial.absorb, Impl.Argon2.X86_64.Initial.finish,
    Impl.Argon2.X86_64.HPrime.init, Impl.Argon2.X86_64.HPrime.absorbFixed,
    Impl.Argon2.X86_64.HPrime.update, Impl.Argon2.X86_64.HPrime.finalize, Code.allInstrs]
  rw [init, update, finalize]
  lit_decide

theorem memory_mxcsr (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)).allInstrs property = true := by
  simp only [Impl.Argon2.X86_64.MemoryInit.code, Impl.Argon2.X86_64.MemoryInit.clear,
    Impl.Argon2.X86_64.MemoryInit.lane, Impl.Argon2.X86_64.MemoryInit.block, Code.allInstrs]
  rw [HPrime.code_mxcsr v]
  lit_decide

theorem frame_mxcsr (body : Prog isa) (rs : List Reg) (h : body.allInstrs property = true) :
    (Impl.Argon2.X86_64.Derive.frame body rs).allInstrs property = true := by
  induction rs with
  | nil => simpa [Impl.Argon2.X86_64.Derive.frame, Code.allInstrs, loadsMxcsr] using h
  | cons r rs ih => simpa [Impl.Argon2.X86_64.Derive.frame, Code.allInstrs, loadsMxcsr] using ih

theorem code_mxcsr (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)).allInstrs property = true := by
  unfold Impl.Argon2.X86_64.Derive.code
  apply frame_mxcsr
  simp only [Impl.Argon2.X86_64.Derive.body, Impl.Argon2.X86_64.InitialBody.code,
    Impl.Argon2.X86_64.InitFill.code, Impl.Argon2.X86_64.FillFinish.code,
    Impl.Argon2.X86_64.Finish.code, Impl.Argon2.X86_64.FinalOutput.code, Code.allInstrs]
  rw [initial_mxcsr v, memory_mxcsr v name, HPrime.code_mxcsr v]
  lit_decide

end VG.Proof.Argon2.X86_64.Derive
