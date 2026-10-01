import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceLane
import VerifiedGarbage.Proof.Argon2.X86_64.Divide
import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT

/-! # Secret J₂ does not affect the lane-selection trace -/

namespace VG.Proof.Argon2.X86_64.ReferenceLane

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceLane

structure Prefix (s t : State) : Prop where
  high : t.gpr .rdi = s.gpr .rdi >>> 32
  original : t.gpr .r11 = s.gpr .rdi
  keeps : Divide.Keeps [.rdi, .r11] s t

theorem highArgs_ok (s : State) : WP isa (.block highArgs) s (Prefix s) := by
  apply WP.of_runBlock
  simp only [highArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg,
    show 1 ≤ (32 : Nat) ∧ (32 : Nat) ≤ 63 from by decide,
    and_self, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

def changed : List Reg := [.rdi, .r11] ++ Divide.changed

theorem code_ok (s : State) (lo : 0 < (s.gpr .rsi).toNat)
    (bound : (s.gpr .rsi).toNat < 2 ^ 32) :
    WP isa code s fun t =>
      (t.gpr .r8).toNat = (s.gpr .rdi >>> 32).toNat % (s.gpr .rsi).toNat ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((highArgs_ok s).mono ?_)
  intro a ha
  have si := ha.keeps.regs .rsi (by decide)
  refine (Divide.code_ok a ?_ (by rw [si]; exact lo) (by rw [si]; exact bound)).mono ?_
  · rw [ha.high]
    simpa only [show 64 - 32 = (32 : Nat) from rfl] using
      BitVec.toNat_ushiftRight_lt (s.gpr .rdi) 32 (by decide)
  · intro t ht
    refine ⟨?_, ?_, (ha.keeps.mono ?_).trans (ht.2.2.mono ?_)⟩
    · rw [ht.2.1, ha.high, si]
    · exact (ht.2.2.regs .r11 (by decide)).trans ha.original
    · intro r hr; exact List.mem_append_left _ hr
    · intro r hr; exact List.mem_append_right _ hr

theorem highArgs_secret_rel : RelCT isa (fun _ _ => True) (.block highArgs) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  highArgs_secret_rel.seq Divide.code_secret_rel

end VG.Proof.Argon2.X86_64.ReferenceLane
