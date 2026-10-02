import VerifiedGarbage.Proof.AesGcm.Arm.Contract

/-!
# AES-GCM on ARMv7: the stack arguments, and the entry of the functions

Untrusted: everything here is checked by Lean. The functions other than
`init` load `W` from the stack (`ldr r12, [sp, #off]`) and save our caller's
registers there (`entry_ok`); they read their other stack arguments when they
need them, which no write changes (`arg_frame`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)

theorem stackArg_eq (s : State) (k : Nat) :
    stackArg s k = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * k))) 32 := rfl

theorem stackArg_zero (s : State) : stackArg s 0 = s.mem.readW (State.addr s.sp) 32 := by
  simp only [stackArg, stackArgAddr, Nat.mul_zero, add_ofNat_zero]

/-- The stack argument `i` (of `n`) is readable. -/
theorem arg_in {s : State} {n i : Nat} (hi : i < n) (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (h : args s n ∈ s.rd) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
  have e : State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]; exact addr_add (by omega)
  rw [e]; exact in_off (covers_of_mem (List.mem_append_left _ h)) (by omega) (by omega)

/-- The stack arguments stay where they are, outside a frame. -/
theorem arg_frame {s s' : State} {n : Nat} {rs : List Region} (hsp : s'.sp = s.sp)
    (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (hfr : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (args s n).Disjoint r)
    {i : Nat} (hi : i < n) : stackArg s' i = stackArg s i := by
  have e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]; exact addr_add (by omega)
  have hs : Region.Sub ⟨stackArgAddr s i, 4⟩ (args s n) := by rw [e]; exact Offset.sub_base _ (by omega)
  simp only [stackArg, show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]
  exact hfr.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left hs) (by decide)

/-- The entry: `W` loaded from the stack into `r12`, and our caller's
registers saved there. -/
theorem entry_ok {s : State} {off : Nat} (hoff : off < 4096)
    (harg : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (hfit : (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32).toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32), 2560⟩] s.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .r12 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 →
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      SavedAt s'.mem (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32) s →
      Frame [savedR (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)] s.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp .r12 off :: (save .r12 ++ rest))) s Q := by
  rw [← List.singleton_append]
  refine WP.block_append (WP.of_runBlock ⟨s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32), ?_, ?_⟩)
  · arun [hoff, harg]
  refine save_ok (s := s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) (b := .r12) (by simp [gpr_setReg]) hfit hw fun s' g rd wr sp sv fr => k s' ?_ ?_ rd wr sp ?_ fr
  · rw [g]; simp [gpr_setReg]
  · intro r hr; rw [g]; simp [gpr_setReg, hr]
  · intro p hp
    rw [sv p hp]
    have : p.1 ≠ .r12 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [gpr_setReg, this]

end VG.Proof.AesGcm.Arm
