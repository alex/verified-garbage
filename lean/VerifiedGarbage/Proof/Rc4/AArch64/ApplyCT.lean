import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Apply
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

structure EntryAgree (a b : State) : Prop where
  sp : a.sp = b.sp
  p : a.gpr .x0 = b.gpr .x0
  data : a.gpr .x1 = b.gpr .x1
  len : a.gpr .x2 = b.gpr .x2
  i : (contextAt a.mem (a.gpr .x0)).i = (contextAt b.mem (b.gpr .x0)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .x0) 258

theorem apply_start_ct : RelCT isa
    (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block [.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0])
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x9, .x12])) := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : ConstantTime isa (fun _ => True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (.block [.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0]) := by
    exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
      (fun _ _ _ _ h => h) (by taint_decide)
  have hagree : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) a b := by
    refine ⟨hab.sp, fun r hr => ?_⟩
    have he : r = .x0 := by simpa only [VG.AArch64.Taint.mem_ofRegs, List.mem_singleton] using hr
    subst r
    exact hab.p
  have htrace := hct a b tr tr' a' b' trivial trivial hagree ea eb
  obtain ⟨_, u, eu, hau⟩ := apply_start a hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := apply_start b hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, _, _, ha0, ha1, ha2, ha12, _, ha9⟩ := hau
  obtain ⟨_, _, _, hb0, hb1, hb2, hb12, _, hb9⟩ := hbv
  refine ⟨htrace, (Exec.sp ea).trans (hab.sp.trans (Exec.sp eb).symm), fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ha0.trans (hab.p.trans hb0.symm)
  · exact ha1.trans (hab.data.trans hb1.symm)
  · exact ha2.trans (hab.len.trans hb2.symm)
  · exact ha9.trans hb9.symm
  · rw [ha12, hb12, hab.i]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree VG.Impl.Rc4.AArch64.apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold VG.Impl.Rc4.AArch64.apply
  refine RelCT.ite ?_ ?_ ?_
  · intro a b ⟨_, _, hab⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hab.len]
  · refine RelCT.taint (A := taint) (Taint.ofRegs []) ?_ (by taint_decide)
    intro a b ⟨⟨_, _, hab⟩, _⟩
    exact ⟨hab.sp, fun r hr => by simp only [VG.AArch64.Taint.mem_ofRegs, List.not_mem_nil] at hr⟩
  · refine RelCT.seq (RelCT.mono apply_start_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
    exact RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x9, .x12])
      (fun _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64
