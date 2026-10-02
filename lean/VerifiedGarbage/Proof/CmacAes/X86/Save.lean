import VerifiedGarbage.Proof.CmacAes.X86.Words
import VerifiedGarbage.Proof.CmacAes.X86.Call

/-!
# AES-CMAC on x86: saving registers and reading the stack arguments

Weakest preconditions of the stores that save registers in the scratch buffer
(`saveList_ok`), of the loads that restore them (`restoreList_ok`), and of
instructions with a stack argument as their source (`wp_arg`, `wp_addArg`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd WP.cons wp_movm wp_store)

/-- The memory after storing the registers `l` (values `g`) at `B + offset`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

theorem saveList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = saveMem s.mem ((s.gpr .eax).setWidth 64) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2⟩ := hl p (by simp)
    refine wp_store (by rw [ea_at']; exact addr_eq h1) h2 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) {L : Nat} (hL : L < 2 ^ 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ L) → Frame [⟨B, L⟩] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base (n := 32 / 8) _ h (by omega))).trans (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem saveMem_congr (m : Mem) (B : Addr) {g g' : Reg → BitVec 32} :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, g p.1 = g' p.1) → saveMem m B g l = saveMem m B g' l := by
  intro l
  induction l generalizing m with
  | nil => intro _; rfl
  | cons p l ih =>
    intro h
    simp only [saveMem]
    rw [h p (List.mem_cons_self ..)]
    exact ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

set_option simprocs false in
/-- Each slot of `saved` holds the register saved there. -/
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (saveMem m B g saved).readW (B + BitVec.ofNat 64 d) 32 = g r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [saved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

theorem saved_bound : ∀ p ∈ saved, 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2080 := by decide

theorem saved_ne_eax : ∀ p ∈ saved, p.1 ≠ .eax := by decide

theorem save_eq : save = saved.map fun p => Instr.store (at_ .eax p.2) p.1 := rfl

/-- Loads of the registers `l` from `eax + offset`, none of them `eax`. -/
theorem restoreList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ .eax ∧ (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_movm (by rw [ea_at']; exact addr_eq h1) h2 fun s₁ u₁ => ?_
    have eb : s₁.gpr .eax = s.gpr .eax := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem restore_eq (i : Nat) :
    restore i = .mov .eax (argOp i) :: (saved.map fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ [] := by
  simp [restore]

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
