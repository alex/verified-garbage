import VerifiedGarbage.Proof.TripleDes.X86.Sbox
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.X86.KeySteps

namespace VG.Proof.TripleDes.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def spillRegion (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 64, 384⟩

def spillSafe : Instr → Bool
  | .mov d _ | .shift _ d _ => d != .ebp
  | .alu .and d _ | .alu .xor d _ => d != .ebp
  | .store m _ => decide (m.base = .ebp ∧
      64 ≤ m.disp ∧ m.disp + 4 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem spillStep_frame (i : Instr) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .ebp = s.gpr .ebp ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case mov d src =>
    have hd : .ebp ≠ d := by intro heq; subst d; simp at h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact ⟨by simp only [gpr_setReg, hd, ite_false], by
      simp only [mem_setReg]; exact Frame.refl _ _⟩
  case alu op d src =>
    cases op <;> simp only [Bool.false_eq_true] at h
    all_goals
      have hd : .ebp ≠ d := by intro heq; subst d; simp at h
      simp only [exec, execAlu, Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨v, _, rfl⟩ := he
      exact ⟨by simp only [gpr_setReg, gpr_arithFlags, hd, ite_false], by
        simp only [mem_setReg, mem_arithFlags]; exact Frame.refl _ _⟩
  case shift op d n =>
    have hd : .ebp ≠ d := by intro heq; subst d; simp at h
    simp only [exec, execShift] at he
    split at he
    · cases op <;> obtain rfl := Option.some.inj he
      all_goals
        exact ⟨by simp only [gpr_setReg, gpr_setFlags, hd, ite_false], by
          simp only [mem_setReg, mem_setFlags]; exact Frame.refl _ _⟩
    · cases he
  case store m r =>
    obtain ⟨hb, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec, State.store32] at he
    split at he
    · simp only [Option.some.injEq] at he
      subst s'
      refine ⟨rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_⟩
      simp only [State.ea, hb]
      change (spillRegion s).Contains (addr (s.gpr .ebp) m.disp) 4
      rw [VG.X86.addr_eq (by omega)]
      exact Offset.contains (addr32 (s.gpr .ebp)) (by omega) (by omega) (by decide)
    · cases he

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .ebp = s.gpr .ebp ∧ Frame [spillRegion s] s.mem s'.mem := by
  induction is generalizing s with
  | nil =>
    rw [runBlock_nil] at he
    obtain rfl := Option.some.inj he
    exact ⟨rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hsafe
    rw [runBlock_cons] at he
    change (exec i s).bind (runBlock isa is) = some s' at he
    obtain ⟨s₁, hi, hrest⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hg, hf⟩ := spillStep_frame i s s₁ fit hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ (by rw [hg]; exact fit) hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

/-- The saved registers and round counter in scratch slots 0–7 are
outside the S-box's frame, as are the key schedule and block data. -/
theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') :
    Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ fit h he).2

end VG.Proof.TripleDes.X86
