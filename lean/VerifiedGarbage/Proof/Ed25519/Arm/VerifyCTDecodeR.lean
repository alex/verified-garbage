import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPoints
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTDecodeSupport

/-! Untrusted: R decoding and its success branch are determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def RDecodeCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a

def RDecodedCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point)
    (q : Option Spec.Ed25519.Point) (s : State) : Prop :=
  RDecodeCTPre m b pk sig challenge a s ∧ DecodeResult b q s

theorem verifyAfterR_ct (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) (q : Option Spec.Ed25519.Point) :
    CT (fun s t => RDecodedCTPre m b pk sig challenge a q s ∧ RDecodedCTPre m b pk sig challenge a q t)
      (decodedThen (.seq (.block (pointTableWrite 7872)) verifyEquationPoints)) (fun _ _ => True) := by
  apply decodedThen_ct q.isSome
  · exact fun _ h => decodeResult_flag h.2
  · intro s t h tr tm
    have kt : VerifyKeep b s t := VerifyKeep.of_rest tr (by decide) tm
    exact ⟨⟨h.1.1.keep kt, tm ▸ h.1.2.1, (congrArg (fun mem => tablePoint mem b 7744) tm).trans h.1.2.2⟩,
      decodeResult_rest tr tm h.2⟩
  · intro yes
    cases q with
    | none => exact Bool.noConfusion yes
    | some r =>
      have hw : CT (fun s t => RDecodedCTPre m b pk sig challenge a (some r) s ∧ RDecodedCTPre m b pk sig challenge a (some r) t)
          (.block (pointTableWrite 7872)) (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t) := by
        apply ctBoth
        · apply ctRegs [.r0] _ (by taint_decide)
          intro s t h reg hr
          rw [List.mem_singleton] at hr
          subst reg
          exact h.1.1.1.ctx.ctx.r0.trans h.2.1.1.ctx.ctx.r0.symm
        · intro s ⟨⟨hp, hl, ha⟩, _, hpoint⟩
          refine WP.mono (pointTableWrite_ok hp.ctx.ctx hl 7872 (by decide) (by decide)) fun t ⟨tk, tl, _, tp⟩ => ?_
          exact ⟨hp.keep (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
            (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans ha, tp.trans hpoint⟩
      exact RelCT.seq hw (verifyEquationPoints_ct m b pk sig challenge a r)

theorem verifyDecodeR_ct (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) :
    CT (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t)
      verifyDecodeR (fun _ _ => True) := by
  have loadPre (s : State) (h : RDecodeCTPre m b pk sig challenge a s) :
      LoadDecodePre b sig (Spec.Ed25519.bytesAt m (State.addr sig) 32) 8132 s :=
    ⟨h.1.ctx.ctx, h.2.1, h.1.ctx.sigHeader, h.1.ctx.sigInput.prefix (by decide), h.1.rBytes⟩
  have hd : CT (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t)
      (.seq (.block (loadHeader 8132)) pointDecode)
      (fun s t => RDecodedCTPre m b pk sig challenge a (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) s ∧
        RDecodedCTPre m b pk sig challenge a (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) t) := by
    apply ctBoth
    · exact (loadDecode_ct b sig _ 8132 (by decide)).mono (fun s t h => ⟨loadPre s h.1, loadPre t h.2⟩) (fun _ _ h => h)
    · intro s hs
      refine WP.mono (loadDecode_ok (loadPre s hs) (by decide)) fun t ht => ?_
      refine ⟨⟨hs.1.keep ht.1, ht.2.1, (ht.2.2.2 7744 (by decide) (by decide)).trans hs.2.2⟩, ?_⟩
      with_reducible exact ht.2.2.1
  exact ctSeqAssoc (RelCT.seq hd (verifyAfterR_ct m b pk sig challenge a _))

end VG.Proof.Ed25519.Arm
