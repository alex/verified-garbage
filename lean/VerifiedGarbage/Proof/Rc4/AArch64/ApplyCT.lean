import VerifiedGarbage.Proof.Rc4.AArch64.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.ApplySetup
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-!
# The PRGA's constant time

Only the pointers, the length and `i` reach the trace: `applyLoad` computes
from `i` the final `i`, the lanes to skip and the base `B`, which agree in
two runs that agree on `i`, and the rest is checked by taint from those.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

structure EntryAgree (a b : State) : Prop where
  sp : a.sp = b.sp
  p : a.gpr .x0 = b.gpr .x0
  data : a.gpr .x1 = b.gpr .x1
  len : a.gpr .x2 = b.gpr .x2
  i : (contextAt a.mem (a.gpr .x0)).i = (contextAt b.mem (b.gpr .x0)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .x0) 258

/-- The registers the rest of the PRGA needs public. -/
def restPublic : List Reg := [.x0, .x1, .x2, .x4, .x5, .x8, .x9]

theorem applyLoad_ct : RelCT isa (fun a b => ReadValid a ∧ ReadValid b ∧ EntryAgree a b)
    (.block applyLoad) (VG.AArch64.Taint.Agree (Taint.ofRegs restPublic)) := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : ConstantTime isa (fun _ => True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block applyLoad) := by
    exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
      (fun _ _ _ _ h => h) (by taint_decide)
  have hagree : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) a b := by
    refine ⟨hab.sp, fun r hr => ?_⟩
    have he : r = .x0 := by simpa only [VG.AArch64.Taint.mem_ofRegs, List.mem_singleton] using hr
    subst r
    exact hab.p
  have htrace := hct a b tr tr' a' b' trivial trivial hagree ea eb
  obtain ⟨_, u, eu, hau⟩ := setupA_ok hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := setupA_ok hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, a9, a4, a5, a8, -, -, -, -, -, -, ag⟩ := hau
  obtain ⟨_, b9, b4, b5, b8, -, -, -, -, -, -, bg⟩ := hbv
  refine ⟨htrace, (Exec.sp ea).trans (hab.sp.trans (Exec.sp eb).symm), fun r hr => ?_⟩
  simp only [restPublic, VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ag _ (by decide), bg _ (by decide), hab.p]
  · rw [ag _ (by decide), bg _ (by decide), hab.data]
  · rw [ag _ (by decide), bg _ (by decide), hab.len]
  · rw [a4, b4, hab.i, hab.len]
  · rw [a5, b5, hab.i]
  · rw [a8, b8, hab.i]
  · rw [a9, b9]

theorem apply_ct : ConstantTime isa ReadValid EntryAgree VG.Impl.Rc4.AArch64.apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold VG.Impl.Rc4.AArch64.apply
  refine RelCT.ite ?_ ?_ ?_
  · intro a b ⟨_, _, hab⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hab.len]
  · refine RelCT.taint (A := taint) (Taint.ofRegs []) ?_ (by taint_decide)
    intro a b ⟨⟨_, _, hab⟩, _⟩
    exact ⟨hab.sp, fun r hr => by simp only [VG.AArch64.Taint.mem_ofRegs, List.not_mem_nil] at hr⟩
  · refine RelCT.seq (RelCT.mono applyLoad_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
    exact RelCT.taint (A := taint) (Taint.ofRegs restPublic) (fun _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64
