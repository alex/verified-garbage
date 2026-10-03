import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
import VerifiedGarbage.Proof.CmacTripleDes.X86.Block
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.X86.Spill

/-!
# TDEA-CMAC on x86: saving and restoring the registers, and the arguments

Untrusted: everything here is checked by Lean. Each function saves our
caller's `ebx`, `esi`, `edi` and `ebp` to bytes `[84, 100)` of the scratch
buffer through `eax` (`save`, a `Spill.saveCode`), and restores them from
there through `ebp`, `ebp` last (`restore`). It loads its arguments from the stack (`wp_arg`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86
open VG.Proof.MdStream.X86 (Upd wp_movm)

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `xor d, [b + o]`. -/
theorem wp_xorma {d b : Reg} {o : Nat} {a : Addr} (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: is)) s Q := by
  subst ha
  exact Wp.wp_xorm rfl hin fun s' u => k s' ⟨u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- `mov d, [esp + 4 + 4 i]`, the stack argument `i` of the entry state `s₀`. -/
theorem wp_arg {d : Reg} {o : Nat} {s₀ : State} (i : Nat) (ho : o = 4 + 4 * i) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hin : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4) (hv : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i)
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (at_ .esp o)) :: is)) s Q :=
  wp_movm (by rw [ea_at', hesp, ho]; rfl) hin fun s' u => k s' (hv ▸ u)

end

/-! ## Saving -/

theorem saved_fits : Spill.Fits 100 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 84 ≤ p.2 ∧ p.2 + 4 ≤ 100 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

/-- A scratch buffer of at least 100 bytes holds the slots. -/
theorem fits_of {S : BitVec 32} {n : Nat} (h : S.toNat + n ≤ 2 ^ 32) (hn : 100 ≤ n) : S.toNat + 100 ≤ 2 ^ 32 := by
  omega

/-- The memory after saving the registers to the scratch buffer at `S`. -/
def savedMem (s₀ : State) (S : BitVec 32) : Mem :=
  Spill.saveMem s₀.mem (S.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved

theorem savedMem_frame (s₀ : State) (S : BitVec 32) :
    Frame [⟨S.setWidth 64 + BitVec.ofNat 64 84, 16⟩] s₀.mem (savedMem s₀ S) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => by
    have h := saved_bound p hp
    rw [show S.setWidth 64 + BitVec.ofNat 64 p.2 = S.setWidth 64 + BitVec.ofNat 64 84 + BitVec.ofNat 64 (p.2 - 84)
      from (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)

/-- Slots unchanged since the registers were saved hold the registers of `s₀`. -/
theorem saved_of {s₀ : State} {S : BitVec 32} {m : Mem}
    (hm : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      m.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = (savedMem s₀ S).readW (S.setWidth 64 + BitVec.ofNat 64 d) 32) :
    Spill.Saved m (S.setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr saved := fun p hp =>
  have h := saved_bound p hp
  (hm _ h.1 h.2).trans (Spill.saveMem_saved_ofNat _ _ _ saved_fits (by decide) p hp)

/-! ## Restoring -/

/-- The registers but `ebp`, and where they are saved. -/
def saved3 : List (Reg × Nat) := [(.ebx, 84), (.esi, 88), (.edi, 92)]

theorem restore_eq : restore = Spill.restoreCode .ebp (saved3 ++ [(.ebp, 96)]) ++ [] := rfl

/-- `restore` from the scratch buffer at `S`, whose slots hold `g`. -/
theorem restore_ok {s : State} {S : BitVec 32} {g : Reg → BitVec 32} (hb : s.gpr .ebp = S)
    (hS : S.toNat + 100 ≤ 2 ^ 32)
    (hr : ∀ d, 84 ≤ d → d + 4 ≤ 100 → InRegions (s.rd ++ s.wr) (S.setWidth 64 + BitVec.ofNat 64 d) 4)
    (hs : Spill.Saved s.mem (S.setWidth 64 + BitVec.ofNat 64 ·) g saved) :
    WP isa (.block restore) s (Spill.Restored s · g saved) := by
  have ha := Spill.addr_eq_of_fits hS saved_fits
  rw [restore_eq]
  refine Spill.restoreBase_ok saved3 (by decide) (fun p hp => ?_)
    (by rw [hb]; exact hs.congr (fun p hp => (ha p hp).symm) fun _ _ => rfl) fun s' u => WP.block_nil u
  have h := saved_bound p hp
  rw [hb, ha p hp]; exact hr _ h.1 h.2

/-- The registers restored from slots holding those of `s₀`, with the stack
pointer and the return address kept. -/
theorem restored {s₀ s s' : State} (h : Spill.Restored s s' s₀.gpr saved) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hret : s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32) :
    abiPreserved s₀ s' :=
  ⟨h.abi (by decide) (by decide) hsp, hret⟩

end VG.Proof.CmacTripleDes.X86
