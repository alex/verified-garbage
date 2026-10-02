import VerifiedGarbage.Proof.Argon2.X86_64.DerivePrivatePublic
import VerifiedGarbage.Proof.Argon2.X86_64.DerivePrepareCT
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFrameCT

/-! The entire entry point leaks only the exact allowance of the shared contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def AbiRelated (s t : State) : Prop := AbiEnvironment s ∧ AbiEnvironment t ∧ AbiPublic s t

def PrologueRelated (a b : State) : Prop := ∃ s t, AbiRelated s t ∧ a = prologueState s ∧ b = prologueState t

theorem body_rel (v : Proof.Blake2.X86_64.Backend) (name : String) :
    RelCT isa PrologueRelated (Impl.Argon2.X86_64.Derive.body name (HPrime.hash v)) (fun _ _ => True) := by
  have preparation := (prepare_rel.mono (P' := PrologueRelated) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      rw [prologue_sp, prologue_sp, h.2.2.sp]) (fun _ _ h => h)).wpDep (F := fun a b =>
        ∃ s, a = prologueState s ∧ AbiEnvironment s ∧ PrivatePrepared a b) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      exact ⟨(prologue_prepare s h.1).mono (fun _ prepared => ⟨s, rfl, h.1, prepared⟩),
        (prologue_prepare t h.2.1).mono (fun _ prepared => ⟨t, rfl, h.2.1, prepared⟩)⟩)
  unfold Impl.Argon2.X86_64.Derive.body
  apply preparation.seq
  apply (RelCT.exists_ (fun p => parameters_body_rel v name p)).mono ?_ (fun _ _ h => h)
  rintro a b ⟨_, x, y, ⟨s, t, h, rfl, rfl⟩,
    ⟨u, hu, _, prepared₁⟩, ⟨w, hw, _, prepared₂⟩⟩
  have left : PrivatePrepared (prologueState s) a := prepared₁
  have right : PrivatePrepared (prologueState t) b := prepared₂
  exact ⟨abiParams s, private_parameters_related h.1 h.2.1 h.2.2 left right⟩

theorem code_ct (v : Proof.Blake2.X86_64.Backend) (name : String) :
    ConstantTime isa (Spec.Argon2.deriveContract X86_64.abi 344).pre
      (Spec.Argon2.deriveContract X86_64.abi 344).pub
      (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) := by
  have full := frame_rel Impl.Argon2.X86_64.Derive.saved _ AbiRelated
    (fun _ _ h => h.2.2.sp) (body_rel v name)
  exact (full.mono (fun s t h =>
    ⟨abi_environment s h.1, abi_environment t h.2.1, abi_public s t h.2.2⟩)
    (fun _ _ h => h)).constantTime

end VG.Proof.Argon2.X86_64.Derive
