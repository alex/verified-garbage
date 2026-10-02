import VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.X86_64.ParametersLit

/-! The complete derivation does not directly write the stack pointer for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

local notation "property" => (fun i => !isa.writesSp i)

theorem initial_spSafe (v : Proof.Blake2.X86_64.Backend) :
    (Impl.Argon2.X86_64.Initial.code (HPrime.hash v)).all property = true := by
  have init : (HPrime.hash v).init.all property = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).all _ = true
    lit_decide
  have update : (HPrime.hash v).update.all property = true := v.updateSpSafe
  have finalize : (HPrime.hash v).finalize.all property = true := v.finalizeSpSafe
  simp only [Impl.Argon2.X86_64.Initial.code, Impl.Argon2.X86_64.Initial.start,
    Impl.Argon2.X86_64.Initial.absorb, Impl.Argon2.X86_64.Initial.finish,
    Impl.Argon2.X86_64.HPrime.init, Impl.Argon2.X86_64.HPrime.absorbFixed,
    Impl.Argon2.X86_64.HPrime.update, Impl.Argon2.X86_64.HPrime.finalize, Code.all]
  rw [init, update, finalize]
  lit_decide

theorem memory_spSafe (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)).all property = true := by
  simp only [Impl.Argon2.X86_64.MemoryInit.code, Impl.Argon2.X86_64.MemoryInit.clear,
    Impl.Argon2.X86_64.MemoryInit.lane, Impl.Argon2.X86_64.MemoryInit.block, Code.all]
  rw [HPrime.spSafe v]
  lit_decide

theorem frame_spSafe (body : Prog isa) (rs : List Reg) (h : body.all property = true)
    (safe : ∀ r ∈ rs, r ≠ .rsp) :
    (Impl.Argon2.X86_64.Derive.frame body rs).all property = true := by
  induction rs with
  | nil =>
    change (true && body.all property && true) = true
    rw [h]; rfl
  | cons r rs ih =>
    change (true && (Impl.Argon2.X86_64.Derive.frame body rs).all property && property (.pop r 1)) = true
    rw [ih (fun q hq => safe q (List.mem_cons_of_mem _ hq))]
    simp only [Bool.true_and]
    change Bool.not ((some r == some Reg.rsp) : Bool) = true
    rw [Bool.not_eq_true', beq_eq_false_iff_ne]
    exact fun eq => safe r (List.mem_cons_self ..) (Option.some.inj eq)

theorem code_spSafe (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)).all property = true := by
  unfold Impl.Argon2.X86_64.Derive.code
  apply frame_spSafe (safe := by decide)
  simp only [Impl.Argon2.X86_64.Derive.body, Impl.Argon2.X86_64.InitialBody.code,
    Impl.Argon2.X86_64.InitFill.code, Impl.Argon2.X86_64.FillFinish.code,
    Impl.Argon2.X86_64.Finish.code, Impl.Argon2.X86_64.FinalOutput.code, Code.all]
  rw [initial_spSafe v, memory_spSafe v name, HPrime.spSafe v]
  lit_decide

end VG.Proof.Argon2.X86_64.Derive
