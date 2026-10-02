import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.TripleDes.X86.Word
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Impl.TripleDes.X86.Key
open VG.Proof.Rc2.X86 (Keep)

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .eax)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    ∃ s', runBlock isa (rotate28 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 32 ∧ Keep [r, .eax] s s' := by
  have hleft : 1 ≤ 32 - n ∧ 32 - n ≤ 31 := by omega
  have hright : 1 ≤ 28 - n ∧ 28 - n ≤ 31 := by omega
  refine ⟨_, by
    simp only [hleft, hright, and_self, rotate28, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, Ne.symm hr, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
      hr, ite_false]
    rw [hx]
    exact VG.Proof.TripleDes.X86.rotate28_word x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr'.1, hr'.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
    · simp only [rd_setReg, rd_arithFlags, rd_setFlags]
    · simp only [wr_setReg, wr_arithFlags, wr_setFlags]

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .esi = (c.rotateLeft n).setWidth 32
  d : s'.gpr .edi = (d.rotateLeft n).setWidth 32
  keep : Keep [.esi, .edi, .eax] s s'

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .esi = c.setWidth 32) (hd : s.gpr .edi = d.setWidth 32)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 5) :
    WP isa (rotate n) s (RotatePost c d n s) := by
  rw [rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, keep₁⟩ := rotate28_ok s .esi (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .edi = d.setWidth 32 := (keep₁.reg .edi (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, keep₂⟩ := rotate28_ok s₁ .edi (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(keep₂.reg .esi (by decide)).trans c₁, d₂, ?_⟩⟩
  refine ⟨?_, keep₂.mem.trans keep₁.mem, keep₂.rd.trans keep₁.rd, keep₂.wr.trans keep₁.wr⟩
  intro r hr
  simp only [List.mem_cons, not_or] at hr
  exact (keep₂.reg r (by simp only [List.mem_cons, hr.2.1,
    hr.2.2, or_self, not_false_eq_true])).trans
    (keep₁.reg r (by simp only [List.mem_cons, hr.1,
      hr.2.2, or_self, not_false_eq_true]))

end VG.Proof.TripleDes.X86.Key
