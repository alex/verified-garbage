import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem init_call_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 5 0)]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.AArch64.Stream.init_verified _).1
    (Proof.Sha512.AArch64.Stream.init_verified _).2.1 rfl
  · intro g v m t _ hs
    have h := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at h
    rw [BitVec.add_zero] at h
    exact init_ready h
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide), hsp⟩

theorem update_call_ct (backend : Backend) (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (.call (Spec.Sha512.updateApi.name ++ backend.suffix) backend.update)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.update_verified.1 backend.updateCT (Whole.update_noFrames backend)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hi ⟨a0, hs (.x1, .const count) (by simp), hs (.x2, p) (by simp),
      hs (.x3, n) (by simp), hs (.x4, .caller 5 192) (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, p)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x3, n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x4, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem finalize_call_ct (backend : Backend) (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L
      [(.x0, .caller 5 0), (.x1, if b then .caller 4 n else .const n),
        (.x2, .frame 192), (.x3, .caller 5 192)]))
      (.call (Spec.Sha512.finalizeApi.name ++ backend.suffix) backend.finalize)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct backend.finalize_verified.1 backend.finalizeCT (Whole.finalize_noFrames backend)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 5 0) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL ⟨a0, hs (.x1, if b then .caller 4 n else .const n) (by simp),
      hs (.x2, .frame 192) (by simp), hs (.x3, .caller 5 192) (by simp)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨call_gpr_eq (p := (.x0, .caller 5 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, if b then .caller 4 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x2, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .caller 5 192)) h (by simp) (by decide), hsp⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.x0, .caller 5 0)] (by decide) (by simp [Whole.valid])
    (by simp [preserved]) (by taint_decide)).seq init_call_ct

theorem update_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : Whole.valid p) (hn : Whole.valid n)
    (hi : Input L (value L p) (value L n))
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup
      [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)])) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (update backend.code backend.suffix (setup
        [(.x0, .caller 5 0), (.x1, .const count), (.x2, p), (.x3, n), (.x4, .caller 5 192)]))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.x0, .caller 5 0), (.x1, .const count),
      (.x2, p), (.x3, n), (.x4, .caller 5 192)] → Whole.valid x.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hc
    · exact hp
    · exact hn
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ (by simp) hv (by simp [preserved]) ht).seq
    (update_call_ct backend count p n hi)

theorem finalize_ct (backend : Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 4096) (b : Bool)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (finalizeArgs n b)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (finalize backend.code backend.suffix n b)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hv : Whole.valid (if b then .caller 4 n else .const n) := by
    cases b <;> simp [Whole.valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.x0, .caller 5 0),
      (.x1, if b then .caller 4 n else .const n), (.x2, .frame 192), (.x3, .caller 5 192)] → Whole.valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · simp [Whole.valid]
    · exact hv
    · simp [Whole.valid]
    · simp [Whole.valid]
  exact (setup_ct hL ha hb _ (by simp) hvall (by simp [preserved]) ht).seq
    (finalize_call_ct backend hL n b)

end VG.Proof.Ed25519.AArch64.SignCached
