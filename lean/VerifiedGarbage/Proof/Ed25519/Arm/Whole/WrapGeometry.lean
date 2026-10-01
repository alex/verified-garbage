import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Framework.Arm.Frame

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

abbrev base (s : State) : BitVec 32 := s.sp - 280
abbrev entered (s : State) : State := allocated 248 (allocated 24 (pushed [.r12] (pushed [.lr] s)))
abbrev bodyRd (s : State) : List Region := s.rd ++ [ARGS (base s)]
abbrev bodyWr (s : State) : List Region := FR (base s) :: s.wr
abbrev stack (s : State) : Region := ⟨State.addr (base s), 280⟩

theorem entered_sp (s : State) : (entered s).sp = base s := by
  change s.sp - 4#32 - 4#32 - 24#32 - 248#32 = s.sp - 280
  simp only [BitVec.sub_sub]
  rfl

theorem base_args (s : State) : base s + 248#32 = s.sp - 4#32 - 4#32 - 24#32 := by
  simp only [base, BitVec.sub_sub]
  change s.sp - 280#32 + 248#32 = s.sp - 32#32
  rw [show (280#32) = 32#32 + 248#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_pad (s : State) : base s + 272#32 = s.sp - 4#32 - 4#32 := by
  simp only [base, BitVec.sub_sub]
  change s.sp - 280#32 + 272#32 = s.sp - 8#32
  rw [show (280#32) = 8#32 + 272#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_lr (s : State) : base s + 276#32 = s.sp - 4#32 := by
  change s.sp - 280#32 + 276#32 = s.sp - 4#32
  rw [show (280#32) = 4#32 + 276#32 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem base_top {s : State} (h : 280 ≤ s.sp.toNat) : (base s).toNat + 280 = s.sp.toNat := by
  change (s.sp - 280#32).toNat + 280 = s.sp.toNat
  rw [BitVec.toNat_sub_of_le (by change 280 ≤ s.sp.toNat; exact h)]
  change s.sp.toNat - 280 + 280 = s.sp.toNat
  omega

theorem base_addr {s : State} (h : 280 ≤ s.sp.toNat) :
    State.addr (base s) = State.addr s.sp - 280 := by
  have e : base s + 280#32 = s.sp := BitVec.sub_add_cancel _ _
  have ha := addr_add (a := base s) (k := 280) (by rw [base_top h]; exact s.sp.isLt)
  rw [e] at ha
  rw [ha]
  exact (BitVec.add_sub_cancel _ _).symm

theorem entered_wr {s : State} (h : 280 ≤ s.sp.toNat) :
    (entered s).wr = FR (base s) :: ARGS (base s) ::
      ⟨State.addr (base s) + 272, 4⟩ :: ⟨State.addr (base s) + 276, 4⟩ :: s.wr := by
  have hb := base_top h
  have hs := s.sp.isLt
  change ⟨State.addr (entered s).sp, 248⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32 - 24#32), 24⟩ ::
    ⟨State.addr (s.sp - 4#32 - 4#32), 4⟩ :: ⟨State.addr (s.sp - 4#32), 4⟩ :: s.wr = _
  rw [entered_sp, ← base_args, ← base_pad, ← base_lr,
    addr_add (by omega), addr_add (by omega), addr_add (by omega)]
  rfl

theorem entered_mem {s : State} (h : 280 ≤ s.sp.toNat) :
    (entered s).mem = (s.mem.writeW (State.addr (base s) + 276) (s.gpr .lr)).writeW
      (State.addr (base s) + 272) (s.gpr .r12) := by
  have hb := base_top h
  have hs := s.sp.isLt
  change (s.mem.writeW (State.addr (s.sp - 4#32)) (s.gpr .lr)).writeW
    (State.addr (s.sp - 4#32 - 4#32)) (s.gpr .r12) = _
  rw [← base_pad, ← base_lr, addr_add (by omega), addr_add (by omega)]
  rfl

end VG.Proof.Ed25519.Arm.Whole
