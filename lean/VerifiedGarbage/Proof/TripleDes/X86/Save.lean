import VerifiedGarbage.Proof.Rc2.X86.Save
import VerifiedGarbage.Proof.TripleDes.X86.RoundStep

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 Keep)

def savedReg (i : Nat) : Reg := savedRegs.getD i .ebp

def scratchArg (s : State) (slot : Nat) : BitVec 32 :=
  s.mem.readW (wordAddr (s.gpr .esp) slot) 32

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (addr32 (current.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 32 =
    original.gpr (savedReg i)

structure SavePost (slot : Nat) (original current : State) : Prop where
  bp : current.gpr .ebp = scratchArg original slot
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  reg : ∀ r, r ≠ .eax → r ≠ .ebp → current.gpr r = original.gpr r
  saved : Saved original current
  frame : Frame [⟨addr32 (scratchArg original slot), 16⟩] original.mem current.mem

theorem saveWithArg_ok (s : State) (slot : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) slot) 4)
    (fit : (scratchArg s slot).toNat + 512 ≤ 2 ^ 32)
    (hw : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s slot) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (saveWithArg slot)) s (SavePost slot s) := by
  have code : saveWithArg slot =
      (([.mov .eax (.mem (memOp .esp (4 * slot)))] : List Instr) ++
        VG.Proof.Rc2.X86.saveCode .eax savedReg 4) ++ [rr .ebp .eax] := by
    unfold saveWithArg
    congr 1
  rw [code, WP.block_append_iff, WP.block_append_iff]
  let s₀ := s.setReg .eax (scratchArg s slot)
  have load : runBlock isa [.mov .eax (.mem (memOp .esp (4 * slot)))] s = some s₀ := by
    have he : exec (.mov .eax (.mem (memOp .esp (4 * slot)))) s = some s₀ := by
      simp only [exec, readSrc, State.load32, State.ea, memOp]
      change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) slot) 4 then
        some (scratchArg s slot) else none).map (s.setReg .eax) = some s₀
      rw [ite_eq_left harg, Option.map_some]
    simp only [runBlock_cons, he, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₀, load, ?_⟩
  have ptr₀ : s₀.gpr .eax = scratchArg s slot := gpr_setReg_self _ _ _
  have hw₀ : ∀ i < 4, InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [ptr₀]; exact hw
  apply WP.mono (VG.Proof.Rc2.X86.saveCode_ok s₀ .eax savedReg 4 (by decide)
    (by rw [ptr₀]; omega) hw₀)
  intro s₁ h₁
  refine WP.of_runBlock ⟨s₁.setReg .ebp (s₁.gpr .eax), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some], ?_⟩
  have ptr₁ : s₁.gpr .eax = scratchArg s slot := by rw [h₁.1]; exact ptr₀
  refine ⟨ptr₁, h₁.2.1, h₁.2.2.1, ?_, ?_, ?_⟩
  · intro r ha hb
    rw [gpr_setReg_of_ne _ _ hb, h₁.1, gpr_setReg_of_ne _ _ ha]
  · intro i hi
    rw [gpr_setReg_self, mem_setReg, ptr₁, h₁.2.2.2, ptr₀]
    rw [VG.Proof.Rc2.X86.saveMem_read _ _ _ 4 (by decide) i hi]
    have hr : savedReg i ≠ .eax := by
      have h : ∀ i < 4, savedReg i ≠ .eax := by decide
      exact h i hi
    exact gpr_setReg_of_ne _ _ hr
  · rw [mem_setReg, h₁.2.2.2, ptr₀]
    exact VG.Proof.Rc2.X86.saveMem_frame _ _ _ 4 (by decide)

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  mem : current.mem = origin.mem
  rd : current.rd = origin.rd
  wr : current.wr = origin.wr
  sp : current.gpr .esp = origin.gpr .esp
  ptr : current.gpr .eax = origin.gpr .ebp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr)
      (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  have code : blockRestore = ([rr .eax .ebp] : List Instr) ++
      VG.Proof.Rc2.X86.restoreCode .eax savedReg (List.range 4) := by
    unfold blockRestore
    congr 1
  rw [code, WP.block_append_iff]
  let s₀ := s.setReg .eax (s.gpr .ebp)
  refine WP.of_runBlock ⟨s₀, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some]
    rfl, ?_⟩
  have hptr : s₀.gpr .eax = s.gpr .ebp := gpr_setReg_self _ _ _
  have hregs : (List.range 4).map savedReg = savedRegs := by decide
  have separate : ∀ i ∈ List.range 4, savedReg i ≠ .eax := by decide
  have h := VG.Proof.Rc2.X86.restoreCode_ok s₀ .eax savedReg (List.range 4)
    original.gpr (by rw [hptr]; omega)
    (fun i hi => by have := List.mem_range.mp hi; omega) separate
    (fun i hi => by rw [hptr]; exact hread i (List.mem_range.mp hi))
    (fun i hi => by rw [hptr]; exact hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  apply WP.mono h
  intro s₁ h₁
  exact ⟨h₁.1, h₁.2.mem, h₁.2.rd, h₁.2.wr,
    (h₁.2.reg .esp (by decide)).trans (gpr_setReg_of_ne s _ (by decide)),
    (h₁.2.reg .eax (by decide)).trans hptr⟩

theorem savedSlot_work_disjoint (s : State) (i : Nat) (hi : i < 4) :
    (⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint (workRegion s) :=
  Offset.disjoint _ (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .ebp = s.gpr .ebp) (hf : Frame [workRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  rw [hbase]
  have hm := hf.readW (a := addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) (w := 32)
    (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i), 4⟩)
    (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact savedSlot_work_disjoint s i hi) (by decide)
  exact hm.trans (hs i hi)

end VG.Proof.TripleDes.X86
