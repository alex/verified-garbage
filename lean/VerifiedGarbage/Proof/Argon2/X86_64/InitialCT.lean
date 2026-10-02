import VerifiedGarbage.Proof.Argon2.X86_64.InitialStartCT
import VerifiedGarbage.Proof.Argon2.X86_64.InitialAbsorbCT
import VerifiedGarbage.Proof.Argon2.X86_64.InitialFinishCT

/-! Complete H₀ is constant time for every verified BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial

theorem code_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa Related (code (HPrime.hash v)) (fun _ _ => True) :=
  (start_rel v).seq
    ((absorb_rel v passwordOffset passwordLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v saltOffset saltLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v secretOffset secretLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
    ((absorb_rel v adOffset adLenOffset (by decide) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩).seq
      (finish_rel v)))))

end VG.Proof.Argon2.X86_64.Initial
