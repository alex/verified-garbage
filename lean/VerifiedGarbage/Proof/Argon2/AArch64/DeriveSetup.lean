import VerifiedGarbage.Proof.Argon2.AArch64.DeriveEntry
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveStores
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveScratch
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompress

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def arguments : List (Nat × Reg) :=
  [(72, .x5), (80, .x4), (88, .x3), (96, .x2), (104, .x1), (112, .x0), (176, .x6), (184, .x7)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r ∈ [Reg.x0, .x5, .x6, .x7] then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : Entered s t) (r : Reg) :
    t.gpr r = argumentValue s r := by
  unfold argumentValue
  split
  · next hr => exact h.values r hr
  · next hr => exact h.regs r hr

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  scratch : t.gpr .x24 = s.mem.readW (s.gpr .x19 + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x19 → r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x19, 192⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .x19, 192⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 248) 8) :
    WP isa (.block Impl.Argon2.AArch64.Derive.setup) s (SetupDone s) := by
  change WP isa (.block ((([.x0, .x5, .x6, .x7] : List Reg).flatMap
    (fun r => Impl.Argon2.AArch64.Instructions.mov32 r r)) ++
    (arguments.map fun arg => .str .x arg.2 .x19 arg.1) ++
    ([.ldr .x .x24 .x19 248] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ arguments, InRegions a.wr (a.gpr .x19 + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.regs .x19 (by decide)]
    apply frameWrite
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 192 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega)⟩
  refine (stores_values_ok arguments a (by decide) write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .x19 = s.gpr .x19 := by rw [saved.regs, entered.regs .x19 (by decide)]
  have scratchWord : b.mem.readW (b.gpr .x19 + 248) 64 = s.mem.readW (s.gpr .x19 + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .x19 + 248) 64 = a.mem.readW (a.gpr .x19 + 248) 64 at kept
    rw [kept, entered.regs .x19 (by decide), entered.mem]
  refine (scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .x19 (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    ?_⟩
  · exact loaded.sp.trans (saved.sp.trans entered.sp)
  · intro arg ha
    rw [loaded.mem, loaded.regs .x19 (by decide), values arg ha]
    exact entered.argument arg.2
  · intro r hr hb hx
    have other : ∀ r ∈ FillCompress.loopRegs, r ∉ [Reg.x0, .x5, .x6, .x7] := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r (other r hr)
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.regs .x19 (by decide)] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 192 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.AArch64.Derive
