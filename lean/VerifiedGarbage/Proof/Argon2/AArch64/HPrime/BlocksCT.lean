import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! # H′: constant time of public argument handling and copying -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime

def publicRegs : List Reg := [.x24, .x20, .x21, .x22, .x23]
def AgreeRegs (rs : List Reg) (s t : State) : Prop :=
  s.sp = t.sp ∧ ∀ r ∈ rs, s.gpr r = t.gpr r

theorem AgreeRegs.taint {rs : List Reg} {s t : State} (h : AgreeRegs rs s t) :
    AArch64.Taint.Agree (Taint.ofRegs rs) s t :=
  ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem publicRegs_callee : ∀ r ∈ publicRegs, r ∈ preserved := by decide

theorem publicRegs_not_link : ∀ r ∈ publicRegs, r ≠ .x30 := by decide

theorem setup_rel :
    RelCT isa (AgreeRegs [.x0, .x1, .x2, .x3, .x4]) (.block setup)
      (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (AgreeRegs publicRegs) chooseLength
    (AgreeRegs (.x1 :: publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) (.x1 :: publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (AgreeRegs (.x8 :: publicRegs)) copy (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.x8 :: publicRegs))
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (AgreeRegs publicRegs) emitPrefix (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (AgreeRegs publicRegs) copyRemaining (AgreeRegs publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs publicRegs)
    (fun _ _ hp => hp.taint) publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (AgreeRegs [.x24]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.x24]) (fun _ _ hp => hp.taint)
    (by taint_decide)

end VG.Proof.Argon2.AArch64.HPrime
