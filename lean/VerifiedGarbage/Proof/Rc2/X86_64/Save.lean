import VerifiedGarbage.Proof.Rc2.X86_64.BlockIO
import VerifiedGarbage.Proof.Framework.Offset

/-! # Saving and restoring RC2's callee-saved registers in scratch -/

namespace VG.Proof.Rc2.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def saveMem (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) : Mem :=
  (List.range n).foldl (fun m i => m.writeW (p + BitVec.ofNat 64 (8 * i)) (v i)) m

theorem saveMem_succ (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) :
    saveMem m p v (n + 1) = (saveMem m p v n).writeW (p + BitVec.ofNat 64 (8 * n)) (v n) := by
  simp only [saveMem, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem saveMem_read (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) (hn : n ≤ 64)
    (i : Nat) (hi : i < n) : (saveMem m p v n).readW (p + BitVec.ofNat 64 (8 * i)) 64 = v i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [saveMem_succ]
    by_cases he : i = n
    · subst i; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem saveMem_frame (m : Mem) (p : Addr) (v : Nat → BitVec 64) (n : Nat) (hn : n ≤ 64) :
    Frame [⟨p, 8 * n⟩] m (saveMem m p v n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    rw [saveMem_succ]
    have prev : Frame [⟨p, 8 * (n + 1)⟩] m (saveMem m p v n) := by
      apply (ih (by omega)).sub
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      refine ⟨⟨p, 8 * (n + 1)⟩, List.mem_cons_self, ?_⟩
      intro x hx
      change (x - p).toNat + 1 ≤ 8 * n at hx
      change (x - p).toNat + 1 ≤ 8 * (n + 1)
      omega
    exact prev.writeW List.mem_cons_self _ (Offset.contains_base p (by omega) (by omega))

def saveCode (base : Reg) (regs : Nat → Reg) (n : Nat) : List Instr :=
  (List.range n).map fun i => .store (memOp base (8 * i)) (regs i)

theorem saveCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (n : Nat)
    (writable : ∀ i < n, InRegions s.wr (s.gpr base + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (saveCode base regs n)) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = saveMem s.mem (s.gpr base) (fun i => s.gpr (regs i)) n) := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [saveCode, List.range_succ, List.map_append, List.map_cons, List.map_nil, WP.block_append_iff]
    apply WP.mono (ih (fun i hi => writable i (by omega)))
    intro s₁ h₁
    have valid := writable n (by omega)
    have valid₁ : InRegions s₁.wr (s₁.gpr base + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [h₁.1, h₁.2.2.1]; exact valid
    refine WP.of_runBlock ⟨{s₁ with mem := s₁.mem.writeW (s₁.gpr base + BitVec.ofNat 64 (8 * n)) (s₁.gpr (regs n))}, ?_, ?_⟩
    · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
        State.ea, offset_nat, valid₁, ite_true]
    · exact ⟨h₁.1, h₁.2.1, h₁.2.2.1, by rw [h₁.2.2.2, h₁.1, saveMem_succ]⟩

def restoreCode (base : Reg) (regs : Nat → Reg) (is : List Nat) : List Instr :=
  is.map fun i => .mov (regs i) (.mem (memOp base (8 * i)))

theorem restoreCode_ok (s : State) (base : Reg) (regs : Nat → Reg) (is : List Nat)
    (values : Reg → BitVec 64)
    (separate : ∀ i ∈ is, regs i ≠ base)
    (readable : ∀ i ∈ is, InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 (8 * i)) 8)
    (stored : ∀ i ∈ is, s.mem.readW (s.gpr base + BitVec.ofNat 64 (8 * i)) 64 = values (regs i)) :
    WP isa (.block (restoreCode base regs is)) s (fun s' =>
      (∀ r ∈ is.map regs, s'.gpr r = values r) ∧ Keep (is.map regs) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    change WP isa (.block (([.mov (regs i) (.mem (memOp base (8 * i)))] : List Instr) ++ restoreCode base regs is)) s _
    rw [WP.block_append_iff]
    let s₁ := s.setReg (regs i) (values (regs i))
    have hi : i ∈ i :: is := List.mem_cons_self
    refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
    · simp only [memOp, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
        State.ea, offset_nat, readable i hi, ite_true, Option.map_some, stored i hi]
      rfl
    have keep₁ : Keep [regs i] s s₁ := by
      constructor
      · intro r hr
        simp only [List.mem_singleton] at hr
        exact gpr_setReg_of_ne _ _ hr
      · exact mem_setReg _ _ _
      · exact rd_setReg _ _ _
      · exact wr_setReg _ _ _
    have ptr₁ := keep₁.reg base (by
      simp only [List.mem_singleton]; exact Ne.symm (separate i hi))
    have read₁ : ∀ j ∈ is,
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr base + BitVec.ofNat 64 (8 * j)) 8 := by
      rw [keep₁.rd, keep₁.wr, ptr₁]
      exact fun j hj => readable j (List.mem_cons_of_mem _ hj)
    have stored₁ : ∀ j ∈ is,
        s₁.mem.readW (s₁.gpr base + BitVec.ofNat 64 (8 * j)) 64 = values (regs j) := by
      rw [keep₁.mem, ptr₁]
      exact fun j hj => stored j (List.mem_cons_of_mem _ hj)
    apply WP.mono (ih s₁ (fun j hj => separate j (List.mem_cons_of_mem _ hj)) read₁ stored₁)
    intro s₂ h₂
    constructor
    · intro r hr
      simp only [List.map_cons, List.mem_cons] at hr
      by_cases hm : r ∈ is.map regs
      · exact h₂.1 r hm
      · have he := hr.resolve_right hm
        subst r
        rw [h₂.2.reg _ hm]
        exact gpr_setReg_self _ _ _
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem saveMem_frame_le (m : Mem) (p : Addr) (v : Nat → BitVec 64)
    (n capacity : Nat) (hn : n ≤ capacity) (hc : capacity ≤ 64) :
    Frame [⟨p, 8 * capacity⟩] m (saveMem m p v n) := by
  apply (saveMem_frame m p v n (by omega)).sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  refine ⟨⟨p, 8 * capacity⟩, List.mem_cons_self, ?_⟩
  intro x hx
  change (x - p).toNat + 1 ≤ 8 * n at hx
  change (x - p).toNat + 1 ≤ 8 * capacity
  omega

end VG.Proof.Rc2.X86_64
