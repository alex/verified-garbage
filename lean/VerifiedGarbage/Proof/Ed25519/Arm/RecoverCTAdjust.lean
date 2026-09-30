import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverAdjust

/-! The sign-adjustment branch depends only on the public coordinate and sign. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def SignCTPre (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧
    s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat ∧ env s.mem base 0 = x

theorem parityBlockCT_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
      Ctx base t ∧ t.z = (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hc hl 0) fun a ⟨ak, _, _, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun t ⟨tr, _, tz⟩ => ?_
  exact ⟨(ak.ctx hc).of_rest tr (by decide), by rw [tz, av]⟩

theorem adjustTail_ct :
    CT (fun x y => x.gpr .r0 = y.gpr .r0 ∧ x.z = y.z)
      (.seq (.ite .eq (.block []) (fieldCode [.const 5 0, .sub 0 5 0])) recoverSuccess) (fun _ _ => True) := by
  refine RelCT.seq (R := fun (x y : State) => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r)
    (RelCT.ite (fun _ _ h => congrArg some h.2) ?_ ?_) ?_
  · apply ctRegsKeeping [.r0] [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply ctRegsKeeping [.r0] [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.1
  · apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => h

theorem recoverAdjustSign_ct (base : BitVec 32) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t) recoverAdjustSign (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (freeze 0 ++ recoverParity)) (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by taint_decide)
    exact fun _ _ h => r0_agree h.1.1.r0 h.2.1.r0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (freeze 0 ++ recoverParity)) s fun t =>
        Ctx base t ∧ t.z = ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlockCT_ok h.1 h.2.1 b h.2.2.1) fun t ⟨hc, hz⟩ => ?_
    exact ⟨hc, by rw [hz, h.2.2.2]⟩
  have hp := (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h)
    (fun _ _ h => And.intro (h.2.1.1.r0.trans h.2.2.1.r0.symm) (h.2.1.2.trans h.2.2.2.symm))
  exact RelCT.seq hp adjustTail_ct

end VG.Proof.Ed25519.Arm
