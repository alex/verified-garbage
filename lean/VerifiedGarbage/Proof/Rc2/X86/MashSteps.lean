import VerifiedGarbage.Proof.Rc2.X86.MixStep

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem wordOff_mod (s : State) (i : Nat) :
    addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i) = wordBase s + BitVec.ofNat 64 (4 * (i % 4)) := by
  have e : wordOff i = wordOff (i % 4) := by simp [wordOff]
  rw [e]; exact wordOff_eq s _ (Nat.mod_lt _ (by decide))

theorem loadScratchWord_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) (r : Reg) (i : Nat) :
    ∃ s', runBlock isa [.mov r (.mem (memOp .ebp (wordOff i)))] s = some s' ∧
      s'.gpr r = (v.getD (i % 4) 0).setWidth 32 ∧ Keep [r] s s' := by
  have fit := env.scratchFit
  have valid : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (wordOff i)) 4 := by
    rw [wordOff_mod]; exact env.wordRead _ (Nat.mod_lt _ (by decide))
  refine ⟨s.setReg r ((v.getD (i % 4) 0).setWidth 32), ?_, gpr_setReg_self _ _ _, ?_⟩
  · rw [runBlock_cons, exec_load s r .ebp (wordOff i)
      (by simp only [wordOff]; have := Nat.mod_lt i (by decide : 0 < 4); omega) valid,
      wordOff_mod, hv _ (Nat.mod_lt _ (by decide)), runStep_some, runBlock_nil]
  · exact ⟨fun _ hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem mashInput_ok (s : State) (v : Spec.Rc2.State) (hv : MemWords s.mem (wordBase s) v)
    (env : RoundEnv s) (i : Nat) :
    WP isa (.block (mashInput i)) s (fun s' =>
      s'.gpr .eax = (v.getD ((i + 3) % 4) 0).setWidth 32 ∧ s'.gpr .edi = arg s 0 ∧
      Keep [.eax, .edi] s s') := by
  change WP isa (.block (([.mov .eax (.mem (memOp .ebp (wordOff (i + 3))))] : List Instr) ++
    [.mov .edi (.mem (memOp .esp 4))])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := loadScratchWord_ok s v hv env .eax (i + 3)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := loadArg_ok s₁ .edi 0
    (by rw [keep₁.rd, keep₁.wr, argAddr_keep keep₁ (by decide)]; exact env.stackRead)
  refine WP.of_runBlock ⟨s₂, run₂, ?_, ?_, ?_⟩
  · exact (keep₂.reg .eax (by decide)).trans out₁
  · exact out₂.trans (arg_keep keep₁ (by decide) 0)
  · exact (keep₁.weaken (by simp)).trans (keep₂.weaken (by simp))

def mashResult (d : Spec.Rc2.Direction) (x k : BitVec 16) : BitVec 16 :=
  match d with
  | .encrypt => x + k
  | .decrypt => x - k

theorem mashAdjustReg_ok (d : Spec.Rc2.Direction) (s : State) (x k : BitVec 16)
    (hx : s.gpr .edx = x.setWidth 32) (hk : s.gpr .eax = k.setWidth 32) :
    ∃ s', runBlock isa [if d == .decrypt then .alu .sub .edx (.reg .eax) else .alu .add .edx (.reg .eax),
      .alu .and .edx (.imm 65535)] s = some s' ∧
      s'.gpr .edx = (mashResult d x k).setWidth 32 ∧ Keep [.edx] s s' := by
  cases d <;> refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags, ite_true, ite_false]
    rfl, ?_⟩
  all_goals
    constructor
    · rw [gpr_setReg_self, hx, hk, Word32.maskWord]
      simp [mashResult, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
    · constructor
      · intro r hr
        have hn : r ≠ .edx := by simpa only [List.mem_singleton] using hr
        simp only [gpr_setReg, gpr_arithFlags, hn, ite_false]
      · rfl
      · rfl
      · rfl

theorem mashAdjust_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State)
    (hv : MemWords s.mem (wordBase s) v) (env : RoundEnv s) (i : Nat) (hi : i < 4)
    (k : BitVec 16) (hk : s.gpr .eax = k.setWidth 32) :
    WP isa (.block (mashAdjust d i)) s (fun s' =>
      s'.gpr .edx = (mashResult d (v.getD i 0) k).setWidth 32 ∧ Keep [.edx] s s') := by
  change WP isa (.block (([.mov .edx (.mem (memOp .ebp (wordOff i)))] : List Instr) ++
    [if d == .decrypt then .alu .sub .edx (.reg .eax) else .alu .add .edx (.reg .eax),
      .alu .and .edx (.imm 65535)])) s _
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := loadScratchWord_ok s v hv env .edx i
  rw [Nat.mod_eq_of_lt hi] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := mashAdjustReg_ok d s₁ _ k out₁ ((keep₁.reg .eax (by decide)).trans hk)
  exact WP.of_runBlock ⟨s₂, run₂, out₂, keep₁.trans keep₂⟩

end VG.Proof.Rc2.X86
