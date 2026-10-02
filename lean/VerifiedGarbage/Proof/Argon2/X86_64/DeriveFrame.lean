import VerifiedGarbage.Impl.Argon2.X86_64.Derive
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-! Compose the nested saved-register frames and the 120-byte local allocation. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def frameStart (s : State) : List Reg → State
  | [] => pushed (List.replicate 15 .rax) s
  | r :: rs => frameStart (pushed [r] s) rs

def frameEnd (s : State) : List Reg → State
  | [] => popped .rax 15 s
  | r :: rs => popped r 1 (frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.gpr .rsp = (frameStart s rs).gpr .rsp)
    (wr : t.wr = (frameStart s rs).wr) :
    (frameEnd t rs).gpr .rsp = s.gpr .rsp ∧ (frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · rw [frameEnd, popped_rsp, sp, frameStart, pushed_rsp]
      simp only [List.length_replicate, Nat.reduceMul, BitVec.sub_add_cancel]
    · rw [frameEnd, popped_wr, wr, frameStart, pushed_wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed [r] s) sp wr
    constructor
    · rw [frameEnd, popped_rsp, innerSp, pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one, BitVec.sub_add_cancel]
    · rw [frameEnd, popped_wr, innerWr, pushed_wr]; rfl

theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (notSp : .rsp ∉ rs) (space : 120 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (run : WP isa body (frameStart s rs) fun t =>
      t.gpr .rsp = (frameStart s rs).gpr .rsp ∧ t.wr = (frameStart s rs).wr ∧ Q (frameEnd t rs)) :
    WP isa (Impl.Argon2.X86_64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.frame (by decide) (by decide) (by decide) (by simpa using space) run
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have pushedBound : ((pushed [r] s).gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      exact toNat_sub_ofNat (by simp only [List.length_cons] at space; omega)
    have innerSpace : 120 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega
    apply WP.frame (by simp) (by simpa using notSp.1) (Ne.symm notSp.1)
      (by simp only [List.length_cons] at space; simp only [List.length_singleton, Nat.mul_one]; omega)
    apply ih (pushed [r] s) (fun t => t.gpr .rsp = (pushed [r] s).gpr .rsp ∧
      t.wr = (pushed [r] s).wr ∧ Q (popped r 1 t)) notSp.2 innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    obtain ⟨endSp, endWr⟩ := frameEnd_metadata (pushed [r] s) t rs sp wr
    exact ⟨sp, wr, endSp, endWr, result⟩

end VG.Proof.Argon2.X86_64.Derive
