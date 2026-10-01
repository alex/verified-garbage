import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTDecodeR

/-! Untrusted: A decoding and its success branch are determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ADecodedCTPre (m : Mem) (b pk sig challenge : BitVec 32)
    (q : Option Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ DecodeResult b q s

theorem verifyAfterA_ct (m : Mem) (b pk sig challenge : BitVec 32) (q : Option Spec.Ed25519.Point) :
    CT (fun s t => ADecodedCTPre m b pk sig challenge q s ∧ ADecodedCTPre m b pk sig challenge q t)
      (decodedThen (.seq (.block (pointTableWrite 7744)) verifyDecodeR)) (fun _ _ => True) := by
  apply decodedThen_ct q.isSome
  · exact fun _ h => decodeResult_flag h.2.2
  · intro s t h tr tm
    have kt : VerifyKeep b s t := VerifyKeep.of_rest tr (by decide) tm
    exact ⟨h.1.keep kt, tm ▸ h.2.1, decodeResult_rest tr tm h.2.2⟩
  · intro yes
    cases q with
    | none => exact Bool.noConfusion yes
    | some a =>
      have hw : CT (fun s t => ADecodedCTPre m b pk sig challenge (some a) s ∧ ADecodedCTPre m b pk sig challenge (some a) t)
          (.block (pointTableWrite 7744)) (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t) := by
        apply ctBoth
        · apply ctRegs [.r0] _ (by taint_decide)
          intro s t h reg hr
          rw [List.mem_singleton] at hr
          subst reg
          exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
        · intro s ⟨hp, hl, _, hpoint⟩
          refine WP.mono (pointTableWrite_ok hp.ctx.ctx hl 7744 (by decide) (by decide)) fun t ⟨tk, tl, _, tp⟩ => ?_
          exact ⟨hp.keep (VerifyKeep.of_powers tk (by decide) (by decide)), tl, tp.trans hpoint⟩
      exact RelCT.seq hw (verifyDecodeR_ct m b pk sig challenge a)

theorem verifyDecodeA_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) verifyDecodeA (fun _ _ => True) := by
  have loadPre (s : State) (h : VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) :
      LoadDecodePre b pk (Spec.Ed25519.bytesAt m (State.addr pk) 32) 8128 s :=
    ⟨h.1.ctx.ctx, h.2, h.1.ctx.pkHeader, h.1.ctx.pkInput, h.1.pkBytes⟩
  have hd : CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b))
      (.seq (.block (loadHeader 8128)) pointDecode)
      (fun s t => ADecodedCTPre m b pk sig challenge (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) s ∧
        ADecodedCTPre m b pk sig challenge (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) t) := by
    apply ctBoth
    · exact (loadDecode_ct b pk _ 8128 (by decide)).mono (fun s t h => ⟨loadPre s h.1, loadPre t h.2⟩) (fun _ _ h => h)
    · intro s hs
      refine WP.mono (loadDecode_ok (loadPre s hs) (by decide)) fun t ht => ?_
      refine ⟨hs.1.keep ht.1, ht.2.1, ?_⟩
      with_reducible exact ht.2.2.1
  exact ctSeqAssoc (RelCT.seq hd (verifyAfterA_ct m b pk sig challenge _))

end VG.Proof.Ed25519.Arm
