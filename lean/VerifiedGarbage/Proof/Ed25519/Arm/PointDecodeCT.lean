import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTRoot
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode

/-! Strict point decoding leaks only its public encoded bytes and pointers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def DecodeCTPre (base ptr : BitVec 32) (bs : List Byte) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩ ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem pointDecode_ct (base ptr : BitVec 32) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t) pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t)
      pointDecodeLoad (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base ptr bs s) :
      WP isa pointDecodeLoad s fun t => RecoverCTPre base b y t ∧
        t.z = decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P) := by
    obtain ⟨hc, hl, hp, hf, hr, hsep, hbs⟩ := h
    refine WP.mono (pointDecodeLoad_ok hc hl hp hf hr hsep) fun t ⟨kt, lt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.ctx hc, lt, ?_, ?_⟩, ?_⟩
    · rw [tb, hbs]
    · rw [ty, hbs]
    · rw [tz, hbs]
  rw [pointDecode]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (recoverPoint_ct base b y).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .r9 = BitVec.ofNat 32 p.isSome.toNat := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.Arm
