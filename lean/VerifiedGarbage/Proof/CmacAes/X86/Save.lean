import VerifiedGarbage.Proof.CmacAes.X86.Words
import VerifiedGarbage.Proof.CmacAes.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Spill

/-!
# AES-CMAC on x86: saving registers and reading the stack arguments

The registers saved in the scratch buffer (`Spill`, with their slots), and
weakest preconditions of instructions with a stack argument as their source
(`wp_arg`, `wp_addArg`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd WP.cons wp_movm wp_store)

theorem saved_fits : Spill.Fits 2080 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

theorem save_eq : save = Spill.saveCode .eax saved := rfl

theorem restore_eq (i : Nat) : restore i = .mov .eax (argOp i) :: (Spill.restoreCode .eax saved ++ []) := rfl

/-- Each slot of `saved` holds the register saved there. -/
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (Spill.saveMem m (B + BitVec.ofNat 64 ·) g saved).readW (B + BitVec.ofNat 64 d) 32 = g r :=
  Spill.saveMem_saved_ofNat m B g saved_fits (by decide) (r, d) h

/-! ## The stack arguments -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [esp + 4 + 4 i]`, the stack argument `i` of the entry state `s₀`. -/
theorem wp_arg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  wp_movm (by rw [ea_at', hesp]; rfl) hin fun s' u => k s' (hv ▸ u)

/-- `add d, [esp + 4 + 4 i]`. -/
theorem wp_addArg {d : Reg} {i : Nat} {s₀ : State} (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (s.gpr d + arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (argOp i) :: is)) s Q := by
  refine WP.cons (s' := (arithFlags s (s.gpr d + arg s₀ i)
    (2 ^ 32 ≤ (s.gpr d).toNat + (arg s₀ i).toNat) (addOverflow (s.gpr d) (arg s₀ i) (s.gpr d + arg s₀ i))).setReg d
      (s.gpr d + arg s₀ i)) ?_ (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _))
  have ea : s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by rw [ea_at', hesp]; rfl
  simp [exec, execAlu, readSrc, argOp, State.load32, ea, hin, hv]

end

end VG.Proof.CmacAes.X86
