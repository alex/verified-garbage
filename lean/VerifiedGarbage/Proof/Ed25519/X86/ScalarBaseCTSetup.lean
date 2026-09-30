import VerifiedGarbage.Proof.Ed25519.X86.PointCTMul
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseCTLit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseMain

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def baseScalar (s : State) : Nat := Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)

theorem pointCTCtx_saved {s₀ s : State} (h : scalarBaseLocal.pre s₀) (hs : Saved s₀ (arg s₀ 2) s) :
    PointCTCtx (arg s₀ 2) s := by
  obtain ⟨hp, _, ho⟩ := scalarBase_pre h
  refine ⟨hs.ctx hp.fit hp.wr, ?_, ?_, ?_, ?_⟩
  · rw [hs.wr, h.2.1]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · rw [hs.wr, h.2.1]
    exact List.pairwise_cons.mpr ⟨by simpa using ho.sep, by simp⟩
  · intro r hr
    rw [hs.wr, h.2.1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [BitVec.toNat_setWidth]
    · omega_using [ho.fit]
    · omega_using [hp.fit]
  · change s.wr.getD 1 ⟨0, 0⟩ = _
    rw [hs.wr, h.2.1]; rfl

theorem scalarBaseStart_ok {s : State} (h : scalarBaseLocal.pre s) :
    WP isa (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps)) s fun t =>
      Saved s (arg s 2) t ∧ MulCTInput (arg s 2) (baseScalar s) 16 t := by
  obtain ⟨hp, hi, _⟩ := scalarBase_pre h
  have scalar_bound : baseScalar s < 2 ^ (16 * 16) := by
    have hb := decodeLE_lt (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] at hb
    change baseScalar s < 256 ^ 32 at hb
    rw [show 2 ^ (16 * 16) = 256 ^ 32 by decide]
    exact hb
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (abiSave_ok hp) fun a ha => ?_)
  refine WP.block_append (WP.mono (inputBits_ok hp hi ha (by decide) (by decide)) fun b ⟨hb, bits⟩ => ?_)
  have cb := hb.ctx hp.fit hp.wr
  refine WP.mono (fieldCode_ok baseSetupOps cb) fun c ⟨kc, ec⟩ => ?_
  have hc := hb.ikeep hp.fit (IKeep.of_field kc)
  refine ⟨hc, pointCTCtx_saved h hc, scalar_bound, ?_, ?_⟩
  · intro i ii
    rw [IKeep.bit (IKeep.of_field kc) cb i (by omega_using [ii]), bits i (by omega_using [ii]), scalarBit_nat]
    rfl
  · rw [ec, baseSetup_d]

theorem scalarBaseStart_ct : RelCT isa
    (fun s t => scalarBaseLocal.pre s ∧ scalarBaseLocal.pre t ∧ scalarBaseLocal.pub s t)
    (.block (abiSave 2 ++ inputBits 1 32 ++ fieldCode baseSetupOps)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (scalarTaint 2 3) _ (by taint_decide)
  intro s t ⟨hs, ht, hp⟩
  obtain ⟨sp, a0, a1, a2⟩ := hp
  obtain ⟨ps, _, os⟩ := scalarBase_pre hs
  obtain ⟨pt, _, ot⟩ := scalarBase_pre ht
  refine scalarTaint_agree (scalarTaint_wf ps os hs.2.1 hs.2.2.2.2.1)
    (scalarTaint_wf pt ot ht.2.1 ht.2.2.2.2.1) sp ?_ (by decide) hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

end VG.Proof.Ed25519.X86
