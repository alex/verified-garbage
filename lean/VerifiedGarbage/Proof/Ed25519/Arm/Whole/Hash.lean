import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Update
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Sha512.Arm.Stream

private theorem rounds_noFrames (n : Nat) : (Impl.Sha512.Arm.rounds n).noFrames = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Impl.Sha512.Arm.rounds, Code.noFrames, ih, Bool.and_self]

theorem update_noFrames : update.noFrames = true := by
  simp only [update, Impl.MdStream.Arm.update, Impl.MdStream.Arm.updateBody, Impl.MdStream.Arm.fill,
    Impl.MdStream.Arm.compressN, Impl.MdStream.Arm.compressWith,
    Impl.Sha512.Arm.compress, Impl.Sha512.Arm.body, Code.noFrames, Bool.and_self]
  rw [rounds_noFrames]; rfl

theorem finalize_noFrames : finalize.noFrames = true := by
  simp only [finalize, Impl.MdStream.Arm.finalize, Impl.MdStream.Arm.finalizeBody,
    Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith,
    Impl.Sha512.Arm.compress, Impl.Sha512.Arm.body, Code.noFrames, Bool.and_self]
  rw [rounds_noFrames]; rfl

variable {E : BitVec 32} {g : Reg → BitVec 32}
  {m₀ : Mem} {rd wr : List Region} {t : State}

theorem init_call (hc : Ctx E g m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : (Proof.Sha512.initArm Spec.Sha512.H0_512).pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr : BitVec 32} (ha : t.gpr .r0 = scr) :
    WP isa (.call Spec.Sha512.init512Api.name (init Spec.Sha512.H0_512)) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr scr) [] := by
  refine call_ok hc (Proof.Sha512.Arm.Stream.init_verified _).1 rfl hp hcov hw
    fun u hu hf hpost => ⟨hu,hf,?_⟩
  change Spec.Sha512.Repr _ u.mem (State.addr (t.callEntry.gpr .r0)) [] at hpost
  rw [State.callEntry_gpr _ (by decide),ha] at hpost
  exact hpost

theorem update_call (hc : Ctx E g m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.updateArm.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr p len : BitVec 32} {prev : List Byte}
    (h0 : t.gpr .r0 = scr) (hdata : stackArg t 0 = p) (hlen : stackArg t 1 = len)
    (hcount : Proof.Sha512.countArm t = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr scr) prev) :
    WP isa (.call Spec.Sha512.updateApi.name update) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (State.addr scr)
        (prev ++ Spec.Ed25519.bytesAt t.mem (State.addr p) len.toNat) := by
  refine call_ok hc Proof.Sha512.Arm.Stream.Update.update_verified.1 update_noFrames hp hcov hw
    fun u hu hf hpost => ⟨hu,hf,?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .r0 = scr := by
    rw [State.withRegions_gpr,State.callEntry_gpr _ (by decide),h0]
  have hcount' : Proof.Sha512.countArm (t.callEntry.withRegions rd' wr') = BitVec.ofNat 64 prev.length := by
    simpa only [Proof.Sha512.countArm,State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] using hcount
  have hh := hpost Spec.Sha512.H0_512 prev (by rw [h0']; exact hr) hcount'
  change Spec.Sha512.Repr _ u.mem (State.addr (t.callEntry.gpr .r0))
    (prev ++ Spec.Ed25519.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat) at hh
  rw [State.callEntry_gpr _ (by decide),h0,hdata,hlen] at hh
  exact hh

theorem finalize_call (hc : Ctx E g m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr out : BitVec 32} {msg : List Byte}
    (h0 : t.gpr .r0 = scr) (hout : stackArg t 0 = out)
    (hcount : Proof.Sha512.countArm t = BitVec.ofNat 64 msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (State.addr scr) msg) (hlen : msg.length < 2^64) :
    WP isa (.call Spec.Sha512.finalizeApi.name finalize) t fun u =>
      Ctx E g m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Ed25519.bytesAt u.mem (State.addr out) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  refine call_ok hc Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1 finalize_noFrames hp hcov hw
    fun u hu hf hpost => ⟨hu,hf,?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .r0 = scr := by
    rw [State.withRegions_gpr,State.callEntry_gpr _ (by decide),h0]
  have hcount' : Proof.Sha512.countArm (t.callEntry.withRegions rd' wr') = BitVec.ofNat 64 msg.length := by
    simpa only [Proof.Sha512.countArm,State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] using hcount
  have hh := hpost Spec.Sha512.H0_512 msg (by rw [h0']; exact hr) hlen hcount'
  change Spec.Ed25519.bytesAt u.mem (State.addr (stackArg t 0)) 64 = _ at hh
  rw [hout] at hh
  exact hh

end VG.Proof.Ed25519.Arm.Whole
