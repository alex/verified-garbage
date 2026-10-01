import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CTReady

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 4 0)] []))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl
  · intro g m t _ hs
    have h := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at h
    rw [BitVec.add_zero] at h
    exact init_ready hL h
  · intro a b ar aw br bw h
    exact call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs])

theorem update_call_ct (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 4 192]))
      (.call Spec.Sha512.updateApi.name Impl.Sha512.Arm.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1
    Proof.Sha512.Arm.Stream.Update.update_verified.2.1 Whole.update_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs.1 (.r2, .const count) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by simp), hs.2 1 (by simp), hs.2 2 (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by simp), stack_arg_eq h (j := 1) (by simp), stack_arg_eq h (j := 2) (by simp)⟩

theorem finalize_call_ct (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 4 0), (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)]
      [.frame 184, .caller 4 192]))
      (.call Spec.Sha512.finalizeApi.name Impl.Sha512.Arm.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1
    Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1 Whole.finalize_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0,
      hs.1 (.r2, if b then .caller 2 n else .const n) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by decide), hs.2 1 (by decide)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, if b then .caller 2 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by decide), stack_arg_eq h (j := 1) (by decide)⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 4 0)] [] (by decide) (by simp [valid])
    (by decide) (by simp) (by simp [preserved])).seq (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : valid p) (hn : valid n)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 4 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] →
      valid x.2 := by simp [valid,hc]
  have hvs : ∀ v ∈ [p,n,Value.caller 4 192], valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [valid]
  exact (setup_ct hL ha hb _ _ (by simp) hv (by simp) hvs (by simp [preserved])).seq
    (update_call_ct hL count p n hi)

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 256) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : valid (if b then .caller 2 n else .const n) := by
    cases b <;> simp [valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .caller 4 0),
      (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)] → valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · simp [valid]
    · exact hv
    · simp [valid]
  exact (setup_ct hL ha hb _ _ (by simp) hvall (by decide) (by simp [valid])
    (by simp [preserved])).seq (finalize_call_ct hL n b)

end VG.Proof.Ed25519.Arm.VerifyMessage
