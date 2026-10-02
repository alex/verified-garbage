import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.AArch64.Divide
import VerifiedGarbage.Proof.Argon2.AArch64.DivideCT

/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.AArch64.ReferenceLane

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceLane
open VG.Impl.Argon2.AArch64

structure Prefix (s t : State) : Prop where
  high : t.gpr .x0 = s.gpr .x0 >>> 32
  original : t.gpr .x7 = s.gpr .x0
  keeps : Divide.Keeps [.x0, .x7, .x15] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, Instructions.mov, Instructions.shr, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 32 < 64 from by decide, show 0 < 4096 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

def changed : List Reg := [.x0, .x7, .x15] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x0 >>> 32).toNat % (s.gpr .x1).toNat ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .x1 (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .x0) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .x7 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun s t => s.sp = t.sp) (.block highArgs)
    (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.AArch64.ReferenceLane
