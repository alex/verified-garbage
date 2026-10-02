import VerifiedGarbage.Proof.TripleDes.AArch64.Sbox
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def spillRegion (s : State) : Region := ⟨s.gpr .x2 + BitVec.ofNat 64 32, 384⟩

def spillSafe : Instr → Bool
  | .addImm .x d _ _ | .subImm .x d _ _ | .movz .x d _ _
  | .logic _ .x d _ _ | .ldr .x d _ _ => d != .x2
  | .str .x _ n off => decide (n = .x2 ∧ 32 ≤ off ∧ off + 8 ≤ 416)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem write_frame (s : State) (d : Reg) (v : BitVec 64) (hd : d ≠ .x2) :
    (s.write .x d v).gpr .x2 = s.gpr .x2 ∧
      Frame [spillRegion s] s.mem (s.write .x d v).mem := by
  exact ⟨gpr_write_of_ne _ _ _ (Ne.symm hd), by
    rw [mem_write]; exact Frame.refl _ _⟩

theorem spillStep_frame (i : Instr) (s s' : State)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .x2 = s.gpr .x2 ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case addImm sz d n imm | subImm sz d n imm | movz sz d imm hw =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ .x2 := by simpa using h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    exact write_frame _ _ _ hd
  case logic op sz d n m =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ .x2 := by simpa using h
    simp only [exec, Option.some.injEq] at he
    subst s'
    exact write_frame _ _ _ hd
  case ldr sz d n off =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ .x2 := by simpa using h
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨a, _, v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case str sz t n off =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec, addr, Size.bytes] at he
    split at he <;> [skip; cases he]
    simp only [Option.bind_some, State.store] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    change Frame [spillRegion s] s.mem (s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 off) (s.gpr t))
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    exact Offset.contains (s.gpr .x2) (by omega) (by omega) (by decide)

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .x2 = s.gpr .x2 ∧ Frame [spillRegion s] s.mem s'.mem := by
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
    obtain ⟨hg, hf⟩ := spillStep_frame i s s₁ hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (he : runBlock isa (sboxCode i) s = some s') :
    Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ h he).2

end VG.Proof.TripleDes.AArch64
