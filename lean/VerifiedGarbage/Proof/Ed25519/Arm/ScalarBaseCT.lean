import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTEngine
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseSetup

/-! The public ABI pointers survive the secret base-point computation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BaseWrapCTPre (b p out : BitVec 32) (s : State) : Prop :=
  scalarBaseLocal.pre s ∧ s.gpr .r0 = out ∧ s.gpr .r1 = p ∧ s.gpr .r2 = b

def BaseWorkCTPre (b p out : BitVec 32) (s : State) : Prop :=
  BaseCTPre b p s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

def BaseFinishCTPre (b out : BitVec 32) (s : State) : Prop :=
  Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 48) 32 = out

theorem scalarBaseSetup_ct (b p out : BitVec 32) :
    CT (fun x y => BaseWrapCTPre b p out x ∧ BaseWrapCTPre b p out y)
      (.block scalarBaseSetup) (fun x y => BaseWorkCTPre b p out x ∧ BaseWorkCTPre b p out y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  · intro s ⟨h, ho, hp, hb⟩
    have hs := ScalarBasePre.of h
    refine WP.mono (scalarBaseSetup_ok hs) fun t ⟨hc, hptr, _, hout, hr, _⟩ => ?_
    have hi : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hs.rd]; simp
    have ht : BaseWorkCTPre (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) t := by
      refine ⟨⟨hc, hptr, hs.f1, ?_, hs.scalar_ws⟩, hout⟩
      intro i hib
      rw [hr.rd, hr.wr]
      exact in_base hi (by omega) (by omega)
    rw [ho, hp, hb] at ht
    exact ht

theorem scalarBaseWork_ct (b p out : BitVec 32) :
    CT (fun x y => BaseWorkCTPre b p out x ∧ BaseWorkCTPre b p out y)
      scalarBaseEngine (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y) := by
  apply ctBoth
  · exact (scalarBaseEngine_ct b p).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  · intro s ⟨⟨hc, hp, hf, hr, hsep⟩, ho⟩
    refine WP.mono (scalarBaseEngine_ok hc hp hf hr hsep) fun t ⟨tk, _, _⟩ => ?_
    exact ⟨tk.ctx hc, (tk.word 48 (.inl rfl) (by decide)).trans ho⟩

theorem scalarBaseFinish_ct (b out : BitVec 32) :
    CT (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y)
      (.block scalarBaseFinish) (fun _ _ => True) := by
  have hh : CT (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y)
      (.block [.ldr .r12 .r0 48])
      (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = out) ∧ (y.gpr .r0 = b ∧ y.gpr .r12 = out)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, ho⟩
      refine ldr0_ok hc (by decide) fun t ht => WP.block_nil ?_
      exact ⟨(ht.other _ (by decide)).trans hc.r0, ht.gpr.trans ho⟩
  change CT _ (.block (([.ldr .r12 .r0 48] : List Instr) ++ (packField FR 0 ++ scalarRestore))) _
  refine ctBlockAppend hh ?_
  apply ctRegs [.r0, .r12] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  have hct (b p out : BitVec 32) :
      CT (fun x y => BaseWrapCTPre b p out x ∧ BaseWrapCTPre b p out y) scalarBase (fun _ _ => True) :=
    RelCT.seq (scalarBaseSetup_ct b p out) (RelCT.seq (scalarBaseWork_ct b p out) (scalarBaseFinish_ct b out))
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2⟩ ex ey
  exact (hct (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl⟩, ⟨ht, h0.symm, h1.symm, h2.symm⟩⟩ ex ey).1

end VG.Proof.Ed25519.Arm
