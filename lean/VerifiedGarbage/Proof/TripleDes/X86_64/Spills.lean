import VerifiedGarbage.Proof.TripleDes.X86_64.Sbox
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

def spillRegion (s : State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 64, 384⟩

def spillSafe : Instr → Bool
  | .mov d _ | .movImm64 d _ => d != .rdx
  | .alu .and d _ | .alu .xor d _ => d != .rdx
  | .store m _ => decide (m.base = .rdx ∧ m.index = none ∧
      64 ≤ m.disp ∧ m.disp + 8 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem spillStep_frame (i : Instr) (s s' : State)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .rdx = s.gpr .rdx ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case mov d src =>
    have hd : .rdx ≠ d := by intro heq; subst d; simp at h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact ⟨by simp only [gpr_setReg, hd, ite_false], by
      simp only [mem_setReg]; exact Frame.refl _ _⟩
  case movImm64 d v =>
    have hd : .rdx ≠ d := by intro heq; subst d; simp at h
    simp only [exec, Option.some.injEq] at he
    subst s'
    exact ⟨by simp only [gpr_setReg, hd, ite_false], by
      simp only [mem_setReg]; exact Frame.refl _ _⟩
  case alu op d src =>
    cases op <;> simp only [Bool.false_eq_true] at h
    all_goals
      have hd : .rdx ≠ d := by intro heq; subst d; simp at h
      simp only [exec, execAlu, Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨v, _, rfl⟩ := he
      exact ⟨by simp only [gpr_setReg, gpr_arithFlags, hd, ite_false], by
        simp only [mem_setReg, mem_arithFlags]; exact Frame.refl _ _⟩
  case store m r =>
    obtain ⟨hb, hi, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec, State.store64] at he
    split at he
    · simp only [Option.some.injEq] at he
      subst s'
      refine ⟨rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_⟩
      have hnat : m.disp = (m.disp.toNat : Int) := by omega
      simp only [State.ea, hi, hb]
      rw [hnat, BitVec.ofInt_natCast]
      exact Offset.contains (s.gpr .rdx) (by omega) (by omega) (by decide)
    · cases he

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .rdx = s.gpr .rdx ∧ Frame [spillRegion s] s.mem s'.mem := by
  induction is generalizing s with
  | nil =>
    rw [runBlock_nil] at he
    obtain rfl := Option.some.inj he
    exact ⟨rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hsafe
    rw [runBlock_cons] at he
    simp only [runStep, Option.bind_eq_some_iff] at he
    obtain ⟨s₁, hi, hrest⟩ := he
    obtain ⟨hg, hf⟩ := spillStep_frame i s s₁ hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

/-- The saved registers and round counter in scratch slots 0–7 are
outside the S-box's frame, as are the key schedule and block data. -/
theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (he : runBlock isa (sboxCode i) s = some s') :
    Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ h he).2

end VG.Proof.TripleDes.X86_64
