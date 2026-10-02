import VerifiedGarbage.Impl.Argon2.AArch64.Derive
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset

/-! Compose the saved-register frames and the 272-byte local allocation. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

def frameStart (s : State) : List Reg → State
  | [] => allocated 272 s
  | r :: rs => frameStart (pushed r s) rs

def frameEnd (s : State) : List Reg → State
  | [] => freed 272 s
  | r :: rs => popped r (frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.sp = (frameStart s rs).sp)
    (wr : t.wr = (frameStart s rs).wr) :
    (frameEnd t rs).sp = s.sp ∧ (frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · change t.sp + BitVec.ofNat 64 272 = s.sp
      rw [sp]; exact BitVec.sub_add_cancel _ _
    · change t.wr.tail = s.wr
      rw [wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed r s) sp wr
    constructor
    · change (frameEnd t rs).sp + 16 = s.sp
      rw [innerSp]; exact BitVec.sub_add_cancel _ _
    · change (frameEnd t rs).wr.tail = s.wr
      rw [innerWr]; rfl

theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (space : 272 + 16 * rs.length ≤ s.sp.toNat)
    (run : WP isa body (frameStart s rs) fun t =>
      t.sp = (frameStart s rs).sp ∧ t.wr = (frameStart s rs).wr ∧ Q (frameEnd t rs)) :
    WP isa (Impl.Argon2.AArch64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.alloc (by decide) (by simpa using space) (run.mono fun _ h => h.2.2)
  | cons r rs ih =>
    have pushedBound : (pushed r s).sp.toNat = s.sp.toNat - 16 := by
      change (s.sp - 16).toNat = s.sp.toNat - 16
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]
        change 16 ≤ s.sp.toNat
        simp only [List.length_cons] at space; omega)]
      rfl
    have innerSpace : 272 + 16 * rs.length ≤ (pushed r s).sp.toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega
    apply WP.frame (by simp only [List.length_cons] at space; omega)
    apply ih (pushed r s) (fun t => Q (popped r t)) innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    exact ⟨sp, wr, result⟩
end VG.Proof.Argon2.AArch64.Derive
