import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ARMv7: saving registers to memory and restoring them

A function saves registers (the callee-saved ones it uses, say) at offsets of
a base register, `str r, [b, #d]` for each `(r, d)` of a list, and restores
them from there, `ldr r, [b, #d]`. Everything is stated for any list and
proven once, by induction over it; a caller's list is a literal, and its side
conditions (`Slots`, `Restorable`) are closed by `decide`, which evaluates
only `Nat` and `Bool` arithmetic.

* `save_ok`, `restoreList_ok`: the code, with any instructions after it, and
  `save_slots_ok`, `restore_slots_ok` for slots in a range of bytes.
* `saveMem`: the memory after saving, which changes only the slots
  (`saveMem_frame`) and holds the registers in them (`saveMem_saved`).
* `Saved`: memory holding the registers in their slots, as long as a frame
  leaves the slots alone (`Saved.frame`).
-/

namespace VG.Arm.Spill

open VG VG.Arm VG.Arm.RegUpd

/-- The memory after storing the registers of `l` (values `g`) at `B + offset`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

/-- Memory `m` holds each register of `l` (values `g`) at `B + offset`. -/
def Saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) (l : List (Reg × Nat)) : Prop :=
  ∀ p ∈ l, m.readW (B + BitVec.ofNat 64 p.2) 32 = g p.1

/-- Every slot of `l` is separate from every later one. -/
def spaced : List (Reg × Nat) → Bool
  | [] => true
  | p :: l => l.all (fun q => p.2 + 4 ≤ q.2 || q.2 + 4 ≤ p.2) && spaced l

/-- The slots of `l` are separate, within bytes `[lo, hi)` of the base, and
`hi ≤ 4096` (offsets are 12-bit immediates). -/
def Slots (lo hi : Nat) (l : List (Reg × Nat)) : Prop :=
  hi ≤ 4096 ∧ l.all (fun p => lo ≤ p.2 && p.2 + 4 ≤ hi) = true ∧ spaced l = true

instance (lo hi : Nat) (l : List (Reg × Nat)) : Decidable (Slots lo hi l) := by
  unfold Slots; infer_instance

/-- `l` restores each register once, and never the base `b`. -/
def Restorable (b : Reg) (l : List (Reg × Nat)) : Prop :=
  (l.map Prod.fst).Nodup ∧ l.all (fun p => p.1 != b) = true

instance (b : Reg) (l : List (Reg × Nat)) : Decidable (Restorable b l) := by
  unfold Restorable; infer_instance

section
variable {lo hi : Nat} {l : List (Reg × Nat)}

theorem Slots.bound (hs : Slots lo hi l) {p : Reg × Nat} (hp : p ∈ l) :
    lo ≤ p.2 ∧ p.2 + 4 ≤ hi ∧ hi ≤ 4096 := by
  have := List.all_eq_true.mp hs.2.1 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, this.2, hs.1⟩

theorem Slots.tail {p : Reg × Nat} (hs : Slots lo hi (p :: l)) : Slots lo hi l := by
  obtain ⟨h₁, h₂, h₃⟩ := hs
  simp only [List.all_cons, spaced, Bool.and_eq_true] at h₂ h₃
  exact ⟨h₁, h₂.2, h₃.2⟩

theorem Slots.head_sep {p : Reg × Nat} (hs : Slots lo hi (p :: l)) {q : Reg × Nat} (hq : q ∈ l) :
    p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2 := by
  have h := hs.2.2
  simp only [spaced, Bool.and_eq_true, List.all_eq_true] at h
  simpa using h.1 q hq

theorem Restorable.ne {b : Reg} (hr : Restorable b l) {p : Reg × Nat} (hp : p ∈ l) : p.1 ≠ b := by
  simpa using List.all_eq_true.mp hr.2 p hp

end

/-! ## Saving -/

/-- Storing the registers of `l` at offsets of `b`, then running `rest`: the
state is `s` with the registers saved. -/
theorem save_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    WP isa (.block rest) { s with mem := saveMem s.mem (State.addr (s.gpr b)) s.gpr l } Q →
    WP isa (.block (l.map (fun p => Instr.str p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2, h3⟩ := hl p List.mem_cons_self
    refine WP.block_cons_iff.mpr ⟨_, exec_str h1 (by rw [addr_add h2]; exact h3), ?_⟩
    rw [addr_add h2]
    exact ih _ Q (fun q hq => hl q (List.mem_cons_of_mem _ hq)) k

/-- `save_ok`, for a continuation that needs only what saving keeps. -/
theorem saveList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.str p.1 b p.2) ++ rest)) s Q :=
  fun s Q hl k => save_ok l s Q hl (k _ rfl rfl rfl rfl rfl)

/-- `save_ok` with the slots of `l` in bytes `[lo, hi)` of `b`, all writable. -/
theorem save_slots_ok {b : Reg} {rest : List Instr} {lo hi : Nat} {l : List (Reg × Nat)}
    (hs : Slots lo hi l) {s : State} {Q : State → Prop} (hfit : (s.gpr b).toNat + hi ≤ 2 ^ 32)
    (hin : ∀ d, lo ≤ d → d + 4 ≤ hi → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : WP isa (.block rest) { s with mem := saveMem s.mem (State.addr (s.gpr b)) s.gpr l } Q) :
    WP isa (.block (l.map (fun p => Instr.str p.1 b p.2) ++ rest)) s Q :=
  save_ok l s Q (fun p hp => by
    have := hs.bound hp
    exact ⟨by omega, by omega, hin _ this.1 this.2.1⟩) k

/-- `save_slots_ok` for the code alone. -/
theorem save_block_ok {b : Reg} {lo hi : Nat} {l : List (Reg × Nat)} (hs : Slots lo hi l) {s : State}
    (hfit : (s.gpr b).toNat + hi ≤ 2 ^ 32)
    (hin : ∀ d, lo ≤ d → d + 4 ≤ hi → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4) :
    WP isa (.block (l.map (fun p => Instr.str p.1 b p.2))) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = saveMem s.mem (State.addr (s.gpr b)) s.gpr l := by
  rw [← List.append_nil (List.map _ l)]
  exact save_slots_ok hs hfit hin (WP.block_nil ⟨rfl, rfl, rfl, rfl⟩)

/-- Saving changes only bytes of a region containing every slot. -/
theorem saveMem_frame_of (B : Addr) (g : Reg → BitVec 32) {rs : List Region} {R : Region} (hR : R ∈ rs) :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ p ∈ l, R.Contains (B + BitVec.ofNat 64 p.2) 4) →
    Frame rs m (saveMem m B g l)
  | _, [], _ => Frame.refl _ _
  | _, p :: l, hl =>
    ((Frame.refl _ _).writeW hR _ (hl p List.mem_cons_self)).trans
      (saveMem_frame_of B g hR _ l fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-- Saving changes only the first `L` bytes at `B`. -/
theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) {L : Nat} (hL : L < 2 ^ 32)
    (l : List (Reg × Nat)) (hl : ∀ p ∈ l, p.2 + 4 ≤ L) : Frame [⟨B, L⟩] m (saveMem m B g l) :=
  saveMem_frame_of B g List.mem_cons_self m l fun p hp =>
    Offset.contains_base B (hl p hp) (by have := hl p hp; omega)

/-- Saving changes only the slots' bytes `[lo, hi)`. -/
theorem saveMem_frame_slots {lo hi : Nat} {l : List (Reg × Nat)} (hs : Slots lo hi l) (m : Mem) (B : Addr)
    (g : Reg → BitVec 32) : Frame [⟨B + BitVec.ofNat 64 lo, hi - lo⟩] m (saveMem m B g l) :=
  saveMem_frame_of B g List.mem_cons_self m l fun p hp => by
    have := hs.bound hp
    exact Offset.contains B this.1 (by omega) (by omega)

/-- Saving the same values. -/
theorem saveMem_congr (B : Addr) {g g' : Reg → BitVec 32} :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ p ∈ l, g p.1 = g' p.1) → saveMem m B g l = saveMem m B g' l
  | _, [], _ => rfl
  | m, p :: l, h => by
    simp only [saveMem]
    rw [h p List.mem_cons_self]
    exact saveMem_congr B _ l fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- A slot separate from every slot saved is unchanged. -/
theorem saveMem_readW_sep (B : Addr) (g : Reg → BitVec 32) {d : Nat} (hd : d + 4 ≤ 4096) :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ q ∈ l, q.2 + 4 ≤ 4096 ∧ (d + 4 ≤ q.2 ∨ q.2 + 4 ≤ d)) →
    (saveMem m B g l).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32
  | _, [], _ => rfl
  | m, q :: l, h => by
    have hq := h q List.mem_cons_self
    refine (saveMem_readW_sep B g hd _ l fun q' hq' => h q' (List.mem_cons_of_mem _ hq')).trans ?_
    exact Mem.readW_writeW_sep (Offset.sep B hq.2 (by omega) (by omega)) (by decide)

/-- After saving, each slot holds its register. -/
theorem saveMem_saved {lo hi : Nat} (B : Addr) (g : Reg → BitVec 32) :
    ∀ (m : Mem) (l : List (Reg × Nat)), Slots lo hi l → Saved (saveMem m B g l) B g l
  | _, [], _ => fun _ h => nomatch h
  | m, p :: l, hs => by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hp := hs.bound List.mem_cons_self
      refine (saveMem_readW_sep B g (by omega) _ l fun q' hq' => ?_).trans
        (Mem.readW_writeW_self32 _ _ _)
      have := hs.bound (List.mem_cons_of_mem _ hq')
      exact ⟨by omega, hs.head_sep hq'⟩
    · exact saveMem_saved B g _ l hs.tail q hq

/-! ## Saved registers -/

/-- Saved registers stay saved through a frame whose regions are disjoint
from the slots `[lo, hi)`. -/
theorem Saved.frame {m m' : Mem} {B : Addr} {g : Reg → BitVec 32} {lo hi : Nat} {l : List (Reg × Nat)}
    (h : Saved m B g l) (hs : Slots lo hi l) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, hi - lo⟩ r) : Saved m' B g l := by
  intro p hp
  have := hs.bound hp
  refine (hf.readW (r := ⟨B + BitVec.ofNat 64 lo, hi - lo⟩)
    (Offset.contains B this.1 (by omega) (by omega)) hd (by decide)).trans (h p hp)

/-- A register restored from its slot has its saved value. -/
theorem Saved.restored {m : Mem} {B : Addr} {g : Reg → BitVec 32} {l : List (Reg × Nat)}
    (h : Saved m B g l) {s : State} (hs : ∀ p ∈ l, s.gpr p.1 = m.readW (B + BitVec.ofNat 64 p.2) 32) :
    ∀ p ∈ l, s.gpr p.1 = g p.1 :=
  fun p hp => (hs p hp).trans (h p hp)

/-- A register of `l` has the value restored. -/
theorem restored_reg {l : List (Reg × Nat)} {s : State} {g : Reg → BitVec 32}
    (h : ∀ p ∈ l, s.gpr p.1 = g p.1) {r : Reg} (hr : r ∈ l.map Prod.fst) : s.gpr r = g r := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact h p hp

/-- The registers `rs`, all in `l`, have the values restored. -/
theorem restored_of {l : List (Reg × Nat)} {s : State} {g : Reg → BitVec 32}
    (h : ∀ p ∈ l, s.gpr p.1 = g p.1) {rs : List Reg} (hrs : ∀ r ∈ rs, r ∈ l.map Prod.fst) :
    ∀ r ∈ rs, s.gpr r = g r :=
  fun r hr => restored_reg h (hrs r hr)

/-! ## Restoring -/

/-- Loading the registers of `l` from offsets of `b`, which is none of them,
then running `rest`. -/
theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p List.mem_cons_self
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [← addr_add h2] at h3
    refine WP.block_cons_iff.mpr ⟨_, exec_ldr h1 h3, ?_⟩
    rw [addr_add h2]
    have eb : (s.setReg p.1 (s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32)).gpr b = s.gpr b :=
      gpr_setReg_of_ne _ _ (Ne.symm h0)
    refine ih _ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) hm hrd hwr hsp
    · rw [eb]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, gpr_setReg_self]
      · rw [hl' q hq, mem_setReg, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, gpr_setReg_of_ne _ _ hr.1]

/-- `restoreList_ok` from slots in bytes `[lo, hi)` of `b`, all readable, that
hold the values `g`: each register of `l` gets its value, and the others and
the memory are unchanged. -/
theorem restore_slots_ok {b : Reg} {rest : List Instr} {lo hi : Nat} {l : List (Reg × Nat)}
    (hs : Slots lo hi l) (hr : Restorable b l) {s : State} {Q : State → Prop} {g : Reg → BitVec 32}
    (hfit : (s.gpr b).toNat + hi ≤ 2 ^ 32)
    (hin : ∀ d, lo ≤ d → d + 4 ≤ hi → InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (hsv : Saved s.mem (State.addr (s.gpr b)) g l)
    (k : ∀ s', (∀ p ∈ l, s'.gpr p.1 = g p.1) → (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q :=
  restoreList_ok l s Q hr.1 (fun p hp => by
      have := hs.bound hp
      exact ⟨hr.ne hp, by omega, by omega, hin _ this.1 this.2.1⟩)
    fun s' ho => k s' (hsv.restored ho)

/-- `restore_slots_ok` for the code alone. -/
theorem restore_block_ok {b : Reg} {lo hi : Nat} {l : List (Reg × Nat)} (hs : Slots lo hi l)
    (hr : Restorable b l) {s : State} {g : Reg → BitVec 32} (hfit : (s.gpr b).toNat + hi ≤ 2 ^ 32)
    (hin : ∀ d, lo ≤ d → d + 4 ≤ hi → InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (hsv : Saved s.mem (State.addr (s.gpr b)) g l) :
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2))) s fun s' =>
      (∀ p ∈ l, s'.gpr p.1 = g p.1) ∧ (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [← List.append_nil (List.map _ l)]
  exact restore_slots_ok hs hr hfit hin hsv fun s' h₁ h₂ h₃ h₄ h₅ h₆ => WP.block_nil ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- `restoreList_ok`, then the base `b` itself, from offset `d`, last. -/
theorem restoreBase_ok {b : Reg} {rest : List Instr} {l : List (Reg × Nat)} {d : Nat} (hr : Restorable b l)
    {s : State} {Q : State → Prop}
    (hl : ∀ p ∈ l ++ [(b, d)], p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4)
    (k : ∀ s', (∀ p ∈ l ++ [(b, d)], s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ (l ++ [(b, d)]).map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block ((l ++ [(b, d)]).map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  rw [List.map_append, List.append_assoc]
  refine restoreList_ok l s _ hr.1 (fun p hp => ⟨hr.ne hp, hl p (List.mem_append_left _ hp)⟩)
    fun s₁ hl₁ ho hm hrd hwr hsp => ?_
  have hb : b ∉ l.map Prod.fst := fun h => by
    obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    exact hr.ne hp he
  have b₁ : s₁.gpr b = s.gpr b := ho b hb
  obtain ⟨h1, h2, h3⟩ := hl (b, d) (List.mem_append_right _ List.mem_cons_self)
  rw [← b₁, ← hrd, ← hwr] at h3
  rw [← b₁] at h2
  rw [← addr_add h2] at h3
  refine WP.block_cons_iff.mpr ⟨_, exec_ldr h1 h3, ?_⟩
  refine k _ (fun p hp => ?_) (fun r hr' => ?_) (by rw [mem_setReg, hm]) (by rw [rd_setReg, hrd])
    (by rw [wr_setReg, hwr]) (by rw [sp_setReg, hsp])
  · rcases List.mem_append.mp hp with hp | hp
    · have hne : p.1 ≠ b := hr.ne hp
      rw [gpr_setReg_of_ne _ _ hne, hl₁ p hp]
    · rw [List.mem_singleton.mp hp, gpr_setReg_self, addr_add h2, hm, b₁]
  · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton, not_or] at hr'
    rw [gpr_setReg_of_ne _ _ hr'.2, ho r hr'.1]

/-- `restoreBase_ok` from slots in bytes `[lo, hi)` of `b`, all readable,
that hold the values `g`. -/
theorem restoreBase_slots_ok {b : Reg} {rest : List Instr} {lo hi : Nat} {l : List (Reg × Nat)} {d : Nat}
    (hs : Slots lo hi (l ++ [(b, d)])) (hr : Restorable b l) {s : State} {Q : State → Prop}
    {g : Reg → BitVec 32} (hfit : (s.gpr b).toNat + hi ≤ 2 ^ 32)
    (hin : ∀ d, lo ≤ d → d + 4 ≤ hi → InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (hsv : Saved s.mem (State.addr (s.gpr b)) g (l ++ [(b, d)]))
    (k : ∀ s', (∀ p ∈ l ++ [(b, d)], s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ (l ++ [(b, d)]).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block ((l ++ [(b, d)]).map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q :=
  restoreBase_ok hr (fun p hp => by
      have := hs.bound hp
      exact ⟨by omega, by omega, hin _ this.1 this.2.1⟩)
    fun s' ho => k s' (hsv.restored ho)

end VG.Arm.Spill
