import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86_64.Target

/-!
# x86-64: saving registers in memory and restoring them

Code that needs more registers than the caller-saved ones stores the
callee-saved registers it uses at offsets of a base register (a scratch
buffer, or the stack) and loads them back before returning. Given the list
`l` of `(register, offset)` pairs and the base register `b`, the save is
`saveCode b l` (a `mov [b + d], r` per pair, in order) and the restore
`restoreCode b l` (a `mov r, [b + d]` per pair).

* `save_run`, `save_ok`: the save stores each register's value at its slot,
  `saveMem`, and changes nothing else;
* `saveMem_saved`: after it, each slot holds its register (`Saved`), if the
  slots do not overlap (`Slots`); `saveMem_frame`: it writes only the slots;
* `Saved.frame`, `Saved.writeW`: the slots keep their values across a frame
  or a write that misses them;
* `restore_run`, `restore_ok`: the restore loads every register of `l` back
  from `Saved` slots (the base register too, if it comes last), and leaves
  the other registers and everything else as it was. The state stays folded
  (`restoreState`, a `setReg` per pair);
* `save_then`, `restore_then`: the same, followed by more code;
* `calleeSaved_ok`: restoring every callee-saved register but `rsp` meets
  the calling convention's obligation on them.

Everything is proven once, by induction on `l`.
-/

namespace VG.X86_64.Spill

open VG.X86_64.RegUpd

/-- The 8-byte slot at offset `d` of `B`. -/
abbrev slot (B : Addr) (d : Nat) : Addr := B + BitVec.ofNat 64 d

/-- `mov [b + d], r` for each `(r, d)` of `l`. -/
def saveCode (b : Reg) (l : List (Reg × Nat)) : List Instr :=
  l.map fun p => .store { base := b, disp := p.2 } p.1

/-- `mov r, [b + d]` for each `(r, d)` of `l`. -/
def restoreCode (b : Reg) (l : List (Reg × Nat)) : List Instr :=
  l.map fun p => .mov p.1 (.mem { base := b, disp := p.2 })

/-- The memory after storing each register `r` of `l` (value `g r`) at its slot. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) : List (Reg × Nat) → Mem
  | [] => m
  | p :: l => saveMem (m.writeW (slot B p.2) (g p.1)) B g l

/-- Each slot of `l` holds its register's value under `g`. -/
def Saved (m : Mem) (B : Addr) (g : Reg → BitVec 64) (l : List (Reg × Nat)) : Prop :=
  ∀ p ∈ l, m.readW (slot B p.2) 64 = g p.1

/-- The slots of `l` do not overlap, nor wrap around the address space. -/
def Slots (l : List (Reg × Nat)) : Prop :=
  (∀ p ∈ l, p.2 + 8 ≤ 2 ^ 64) ∧ l.Pairwise fun p q => p.2 + 8 ≤ q.2 ∨ q.2 + 8 ≤ p.2

instance (l : List (Reg × Nat)) : Decidable (Slots l) := by unfold Slots; infer_instance

theorem ea_slot (s : State) (b : Reg) (d : Nat) :
    s.ea { base := b, disp := d } = slot (s.gpr b) d := by
  simp only [State.ea, BitVec.ofInt_natCast]

/-! ## The save -/

theorem save_run (b : Reg) (l : List (Reg × Nat)) (s : State)
    (hw : ∀ p ∈ l, InRegions s.wr (slot (s.gpr b) p.2) 8) :
    runBlock isa (saveCode b l) s = some { s with mem := saveMem s.mem (s.gpr b) s.gpr l } := by
  induction l generalizing s with
  | nil => exact runBlock_nil
  | cons p l ih =>
    simp only [saveCode, List.map_cons, runBlock_cons, exec, State.store64, ea_slot,
      hw p List.mem_cons_self, ite_true, runStep_some]
    exact ih _ fun q hq => hw q (List.mem_cons_of_mem _ hq)

theorem save_ok (b : Reg) (l : List (Reg × Nat)) (s : State)
    (hw : ∀ p ∈ l, InRegions s.wr (slot (s.gpr b) p.2) 8) :
    WP isa (.block (saveCode b l)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = saveMem s.mem (s.gpr b) s.gpr l :=
  WP.of_runBlock ⟨_, save_run b l s hw, rfl, rfl, rfl, rfl⟩

/-- The save, then `rest` from the state it leaves. -/
theorem save_then (b : Reg) (l : List (Reg × Nat)) {s : State} {rest : List Instr}
    {Q : State → Prop} (hw : ∀ p ∈ l, InRegions s.wr (slot (s.gpr b) p.2) 8)
    (h : WP isa (.block rest) { s with mem := saveMem s.mem (s.gpr b) s.gpr l } Q) :
    WP isa (.block (saveCode b l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.of_runBlock ⟨_, save_run b l s hw, h⟩)

/-! ## The saved memory -/

/-- `saveMem` writes only inside `r`, if `r` contains every slot. -/
theorem saveMem_frame {r : Region} (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    ∀ l : List (Reg × Nat), (∀ p ∈ l, r.Contains (slot B p.2) 8) →
      Frame [r] m (saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro h
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (h p List.mem_cons_self)).trans
      (ih _ fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- `saveMem` writes only inside `[B, B + L)`. -/
theorem saveMem_frame_base (m : Mem) (B : Addr) (g : Reg → BitVec 64) {L : Nat}
    (l : List (Reg × Nat)) (h : ∀ p ∈ l, p.2 + 8 ≤ L) (hL : L ≤ 2 ^ 64) :
    Frame [⟨B, L⟩] m (saveMem m B g l) :=
  saveMem_frame m B g l fun p hp => Offset.contains_base B (h p hp) (by have := h p hp; omega)

/-- Reading 8 bytes at an offset of `B` that misses every slot. -/
theorem saveMem_readW_sep (m : Mem) (B : Addr) (g : Reg → BitVec 64) {e : Nat}
    (he : e + 8 ≤ 2 ^ 64) :
    ∀ l : List (Reg × Nat), (∀ p ∈ l, p.2 + 8 ≤ 2 ^ 64 ∧ (e + 8 ≤ p.2 ∨ p.2 + 8 ≤ e)) →
      (saveMem m B g l).readW (slot B e) 64 = m.readW (slot B e) 64 := by
  intro l
  induction l generalizing m with
  | nil => intro _; rfl
  | cons p l ih =>
    intro h
    obtain ⟨hp, hsep⟩ := h p List.mem_cons_self
    rw [saveMem, ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)]
    exact Mem.readW_writeW_sep (Offset.sep B hsep he hp) (by decide)

theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    ∀ l : List (Reg × Nat), Slots l → Saved (saveMem m B g l) B g l := by
  intro l
  induction l generalizing m with
  | nil => intro _ _ h; cases h
  | cons p l ih =>
    rintro ⟨hb, hp⟩ q hq
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [saveMem, saveMem_readW_sep _ _ _ (hb _ List.mem_cons_self) _ fun p' hp' =>
        ⟨hb p' (List.mem_cons_of_mem _ hp'), hp.1 p' hp'⟩]
      exact Mem.readW_writeW_self64 _ _ _
    · exact ih _ ⟨fun p' hp' => hb p' (List.mem_cons_of_mem _ hp'), hp.2⟩ q hq

/-! ## Keeping the saved values -/

namespace Saved

variable {m m' : Mem} {B : Addr} {g : Reg → BitVec 64} {l : List (Reg × Nat)}

/-- The slots keep their values outside a frame's regions. -/
theorem frame (h : Saved m B g l) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ p ∈ l, ∀ r ∈ rs, Region.Disjoint ⟨slot B p.2, 8⟩ r) : Saved m' B g l :=
  fun p hp => (hf.readW (Region.contains_self _ _) (hd p hp) (by decide)).trans (h p hp)

/-- The slots keep their values across a write of 8 bytes that misses them. -/
theorem writeW (h : Saved m B g l) {e : Nat} (v : BitVec 64)
    (hd : ∀ p ∈ l, p.2 + 8 ≤ e ∨ e + 8 ≤ p.2) (hb : ∀ p ∈ l, p.2 + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : Saved (m.writeW (slot B e) v) B g l :=
  fun p hp => (Mem.readW_writeW_sep (Offset.sep B (hd p hp) (hb p hp) he) (by decide)).trans (h p hp)

end Saved

/-! ## The restore -/

/-- The state after loading `g r` into each register `r` of `l`, in order. -/
def restoreState (s : State) (g : Reg → BitVec 64) : List (Reg × Nat) → State
  | [] => s
  | p :: l => restoreState (s.setReg p.1 (g p.1)) g l

section
variable (g : Reg → BitVec 64)

theorem restoreState_gpr (s : State) :
    ∀ l : List (Reg × Nat), ∀ r : Reg,
      (restoreState s g l).gpr r = if r ∈ l.map Prod.fst then g r else s.gpr r := by
  intro l
  induction l generalizing s with
  | nil => intro r; simp [restoreState]
  | cons p l ih =>
    intro r
    simp only [restoreState, ih, gpr_setReg, List.map_cons, List.mem_cons]
    by_cases h : r = p.1
    · subst h; simp
    · simp only [h, false_or, ite_false]

theorem restoreState_mem (s : State) :
    ∀ l : List (Reg × Nat), (restoreState s g l).mem = s.mem ∧ (restoreState s g l).rd = s.rd ∧
      (restoreState s g l).wr = s.wr := by
  intro l
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons p l ih => exact ih _

end

theorem restore_run (b : Reg) (l : List (Reg × Nat)) (g : Reg → BitVec 64) (s : State)
    (hb : ∀ p ∈ l.dropLast, p.1 ≠ b)
    (hr : ∀ p ∈ l, InRegions (s.rd ++ s.wr) (slot (s.gpr b) p.2) 8)
    (hs : Saved s.mem (s.gpr b) g l) :
    runBlock isa (restoreCode b l) s = some (restoreState s g l) := by
  induction l generalizing s with
  | nil => exact runBlock_nil
  | cons p l ih =>
    simp only [restoreCode, List.map_cons, runBlock_cons, exec, readSrc, State.load64, ea_slot,
      hr p List.mem_cons_self, ite_true, hs p List.mem_cons_self, Option.map_some, runStep_some]
    cases l with
    | nil => exact runBlock_nil
    | cons q l =>
      have hb' : (s.setReg p.1 (g p.1)).gpr b = s.gpr b :=
        gpr_setReg_of_ne _ _ (Ne.symm (hb p List.mem_cons_self))
      refine ih _ (fun q hq => hb q (List.mem_cons_of_mem _ hq)) (fun q hq => ?_) (fun q hq => ?_)
      · rw [hb', rd_setReg, wr_setReg]; exact hr q (List.mem_cons_of_mem _ hq)
      · rw [hb', mem_setReg]; exact hs q (List.mem_cons_of_mem _ hq)

theorem restore_ok (b : Reg) (l : List (Reg × Nat)) (g : Reg → BitVec 64) (s : State)
    (hb : ∀ p ∈ l.dropLast, p.1 ≠ b)
    (hr : ∀ p ∈ l, InRegions (s.rd ++ s.wr) (slot (s.gpr b) p.2) 8)
    (hs : Saved s.mem (s.gpr b) g l) :
    WP isa (.block (restoreCode b l)) s fun s' =>
      (∀ r ∈ l.map Prod.fst, s'.gpr r = g r) ∧ (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.of_runBlock ⟨_, restore_run b l g s hb hr hs, fun r hr => ?_, fun r hr => ?_,
    restoreState_mem g s l⟩
  · simp only [restoreState_gpr, hr, ite_true]
  · simp only [restoreState_gpr, hr, ite_false]

/-- The restore, then `rest` from the state it leaves. -/
theorem restore_then (b : Reg) (l : List (Reg × Nat)) (g : Reg → BitVec 64) {s : State}
    {rest : List Instr} {Q : State → Prop} (hb : ∀ p ∈ l.dropLast, p.1 ≠ b)
    (hr : ∀ p ∈ l, InRegions (s.rd ++ s.wr) (slot (s.gpr b) p.2) 8)
    (hs : Saved s.mem (s.gpr b) g l) (h : WP isa (.block rest) (restoreState s g l) Q) :
    WP isa (.block (restoreCode b l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.of_runBlock ⟨_, restore_run b l g s hb hr hs, h⟩)

/-- After restoring every callee-saved register but `rsp` (which the code
kept), all of them have their values under `g`. -/
theorem calleeSaved_ok {l : List (Reg × Nat)} {g : Reg → BitVec 64} {s s' : State}
    (h₁ : ∀ r ∈ l.map Prod.fst, s'.gpr r = g r) (h₂ : ∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r)
    (hl : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ l.map Prod.fst) (hsp : s.gpr .rsp = g .rsp) :
    ∀ r ∈ calleeSaved, s'.gpr r = g r := by
  intro r hr
  by_cases hm : r ∈ l.map Prod.fst
  · exact h₁ r hm
  · by_cases hsp' : r = .rsp
    · subst hsp'; rw [h₂ _ hm, hsp]
    · exact absurd (hl r hr hsp') hm

theorem restoreState_calleeSaved {l : List (Reg × Nat)} {g : Reg → BitVec 64} {s : State}
    (hl : ∀ r ∈ calleeSaved, r ≠ .rsp → r ∈ l.map Prod.fst) (hsp : s.gpr .rsp = g .rsp) :
    ∀ r ∈ calleeSaved, (restoreState s g l).gpr r = g r :=
  calleeSaved_ok (fun r hr => by simp only [restoreState_gpr, hr, ite_true])
    (fun r hr => by simp only [restoreState_gpr, hr, ite_false]) hl hsp

end VG.X86_64.Spill
