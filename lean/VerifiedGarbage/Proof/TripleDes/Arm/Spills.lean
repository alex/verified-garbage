import VerifiedGarbage.Proof.TripleDes.Arm.Sbox
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def spillRegion (s : State) : Region := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 60, 388⟩
def spillSafe : Instr → Bool
  | .mov d _ | .dp _ d _ _ | .ldr d _ _ => d != .r2
  | .str _ n off => decide (n = .r2 ∧ 60 ≤ off ∧ off + 4 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem write_frame (s : State) (d : Reg) (v : BitVec 32) (hd : d ≠ .r2) :
    (s.setReg d v).gpr .r2 = s.gpr .r2 ∧ Frame [spillRegion s] s.mem (s.setReg d v).mem :=
  ⟨gpr_setReg_of_ne _ _ (Ne.symm hd), by rw [mem_setReg]; exact Frame.refl _ _⟩

theorem spillStep_frame (i : Instr) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .r2 = s.gpr .r2 ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case mov d op2 =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case dp op d n op2 =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case ldr d n off =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case str t n off =>
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    simp only [State.store32] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    rw [addr_add (by omega_using [fit, hhi])]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr (s.gpr .r2)) (by omega) (by omega) (by decide))

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .r2 = s.gpr .r2 ∧ Frame [spillRegion s] s.mem s'.mem := by
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

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') : Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ fit h he).2
end VG.Proof.TripleDes.Arm
