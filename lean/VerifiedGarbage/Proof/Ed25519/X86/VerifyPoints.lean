import VerifiedGarbage.Proof.Ed25519.X86.PointFromInput
import VerifiedGarbage.Proof.Ed25519.X86.VerifyCombine
import VerifiedGarbage.Proof.Ed25519.X86.PointEqual

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

abbrev verificationScalar (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32)
abbrev verificationChallenge (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64)

theorem verifyLhs_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa verifyLhs s fun t => Saved s₀ (arg s₀ 3) t ∧
      tablePoint t.mem (arg s₀ 3) 7936 = Spec.Ed25519.pointMul (verificationScalar s₀) Spec.Ed25519.basePoint ∧
      tablePoint t.mem (arg s₀ 3) 7680 = tablePoint s.mem (arg s₀ 3) 7680 ∧
      tablePoint t.mem (arg s₀ 3) 7808 = tablePoint s.mem (arg s₀ 3) 7808 := by
  have hc := hs.ctx hp.scratch.fit hp.scratch.wr
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) hc) fun a ⟨ka, ea⟩ => ?_)
  have ha := hs.ikeep hp.scratch.fit (IKeep.of_field ka)
  refine WP.seq (WP.mono (pointFromInput_ok hp.scratch hp.scalar ha (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun b ⟨hb, fb, pb, _⟩ => ?_)
  refine WP.mono (pointTableWrite_ok (hb.ctx hp.scratch.fit hp.scratch.wr) 7936 (by decide) (by decide))
    fun t ⟨kt, ft, pt⟩ => ?_
  refine ⟨hb.of_offset hp.scratch.fit kt ft (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [pt, pb, ea, constPoint_eval]
  · rw [tablePoint_frame hp.scratch.fit ft (by decide) (by decide) (Or.inl (by decide)),
      tablePoint_frame hp.scratch.fit fb (by decide) (by decide) (Or.inr (by decide)),
      field_table_same ka hc 7680 (by decide) (by decide)]
  · rw [tablePoint_frame hp.scratch.fit ft (by decide) (by decide) (Or.inl (by decide)),
      tablePoint_frame hp.scratch.fit fb (by decide) (by decide) (Or.inr (by decide)),
      field_table_same ka hc 7808 (by decide) (by decide)]

theorem verifyRhs_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa verifyRhs s fun t => Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (tablePoint s.mem (arg s₀ 3) 7936)
        (Spec.Ed25519.pointAdd (tablePoint s.mem (arg s₀ 3) 7808)
          (Spec.Ed25519.pointMul (verificationChallenge s₀) (tablePoint s.mem (arg s₀ 3) 7680)))) := by
  have hc := hs.ctx hp.scratch.fit hp.scratch.wr
  refine WP.seq (WP.mono (pointTableRead_ok hc 7680 (by decide) (by decide)) fun a ⟨ka, pa, _⟩ => ?_)
  have ha := hs.ikeep hp.scratch.fit (IKeep.of_field ka)
  refine WP.seq (WP.mono (pointFromInput_ok hp.scratch hp.challenge ha (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun b ⟨hb, fb, pb, db⟩ => ?_)
  have cb := hb.ctx hp.scratch.fit hp.scratch.wr
  refine WP.seq (WP.mono (verifyCombine_ok cb db) fun c ⟨kc, pc, qc⟩ => ?_)
  have hcs := hb.ikeep hp.scratch.fit (IKeep.of_field kc)
  refine WP.mono (pointEqual_ok (hcs.ctx hp.scratch.fit hp.scratch.wr)) fun t ⟨kt, vt⟩ => ?_
  refine ⟨hcs.ikeep hp.scratch.fit (IKeep.of_field kt), ?_⟩
  have bt (o : Nat) (ho : 7680 ≤ o) (hn : o + 128 ≤ 8192) :
      tablePoint b.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o :=
    (tablePoint_frame hp.scratch.fit fb (by decide) hn (Or.inr ho)).trans
      (field_table_same ka hc o (by omega_using [ho]) hn)
  rw [vt, pc, qc, pb, pa, bt 7936 (by decide) (by decide), bt 7808 (by decide) (by decide)]

theorem verifyEquationPoints_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa verifyEquationPoints s fun t => Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord
      (Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul (verificationScalar s₀) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem (arg s₀ 3) 7808)
          (Spec.Ed25519.pointMul (verificationChallenge s₀) (tablePoint s.mem (arg s₀ 3) 7680)))) := by
  refine WP.seq (WP.mono (verifyLhs_ok hp hs) fun a ⟨ha, pa, aa, ra⟩ => ?_)
  refine WP.mono (verifyRhs_ok hp ha) fun t ⟨ht, vt⟩ => ?_
  exact ⟨ht, by rw [vt, pa, aa, ra]⟩

end VG.Proof.Ed25519.X86
