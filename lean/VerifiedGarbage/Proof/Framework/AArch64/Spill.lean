import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AArch64: saving registers in memory and restoring them

Code that saves registers (the caller's callee-saved registers, or values it
needs after a call) stores each of a list of registers at an offset of a base
register, `str x<r>, [x<b>, #d]`, and later loads them back,
`ldr x<r>, [x<b>, #d]`. Given the list of `(register, offset)` pairs:

* `saveCode` and `restoreCode` are that code (`l.map fun (r, d) => …`, as the
  implementations write it);
* `saveMem` is the memory after the saves, and `Saved` says the slots hold
  the registers' values;
* `save_ok` and `restore_ok` are their weakest-precondition rules (the saves
  change only memory; the restores change only the restored registers),
  proved once by induction over the list;
* `saveMem_saved`, `saveMem_frame` and `Saved.frame`/`Saved.sub` are the facts
  callers need about the slots, and `Restored.other` says the registers not in
  the list are unchanged.

`Fits` (the offsets are those of an 8-byte `str`/`ldr` and distinct) and
`Restorable` (the loads restore distinct registers, the base register last if
at all) are side conditions on a literal list, which `decide` proves.
-/

namespace VG.AArch64.Spill

open VG VG.AArch64 VG.AArch64.RegUpd

/-! ## The code -/

/-- Store each register `r` at `[b + d]`. -/
def saveCode (b : Reg) (l : List (Reg × Nat)) : List Instr := l.map fun (r, d) => .str .x r b d

/-- Load each register `r` from `[b + d]`. -/
def restoreCode (b : Reg) (l : List (Reg × Nat)) : List Instr := l.map fun (r, d) => .ldr .x r b d

/-- The offsets are those of an 8-byte `str`/`ldr` (multiples of 8 below
32768), and distinct, so the slots do not overlap. -/
def Fits (l : List (Reg × Nat)) : Prop :=
  (∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 < 32768) ∧ (l.map Prod.snd).Nodup

instance (l : List (Reg × Nat)) : Decidable (Fits l) := by unfold Fits; infer_instance

/-- The registers are distinct, and only the last is the base register `b`,
so every load reads at the base's original value. -/
def Restorable (b : Reg) (l : List (Reg × Nat)) : Prop :=
  (l.map Prod.fst).Nodup ∧ ∀ p ∈ l.dropLast, p.1 ≠ b

instance (b : Reg) (l : List (Reg × Nat)) : Decidable (Restorable b l) := by
  unfold Restorable; infer_instance

/-- Registers `regs 0`, …, `regs (n - 1)` in consecutive slots from offset 0. -/
def slots (regs : Nat → Reg) (n : Nat) : List (Reg × Nat) := (List.range n).map fun i => (regs i, 8 * i)

theorem forall_slots {regs : Nat → Reg} {n : Nat} {P : Reg × Nat → Prop}
    (h : ∀ i < n, P (regs i, 8 * i)) : ∀ p ∈ slots regs n, P p := fun p hp => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact h i (List.mem_range.mp hi)

theorem mem_slots {regs : Nat → Reg} {n i : Nat} (hi : i < n) : (regs i, 8 * i) ∈ slots regs n :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem slots_fst (regs : Nat → Reg) (n : Nat) :
    (slots regs n).map Prod.fst = (List.range n).map regs := by
  simp only [slots, List.map_map]; rfl

/-! ## The slots -/

/-- The memory after storing `g r` at `B + d` for each `(r, d)`, in order. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

/-- The slot at `B + d` of each `(r, d)` holds `g r`. -/
def Saved (B : Addr) (g : Reg → BitVec 64) (l : List (Reg × Nat)) (m : Mem) : Prop :=
  ∀ p ∈ l, m.readW (B + BitVec.ofNat 64 p.2) 64 = g p.1

theorem Fits.tail {p : Reg × Nat} {l : List (Reg × Nat)} (h : Fits (p :: l)) : Fits l :=
  ⟨fun q hq => h.1 q (List.mem_cons_of_mem _ hq), (List.nodup_cons.mp h.2).2⟩

theorem saveMem_saved {l : List (Reg × Nat)} (hf : Fits l) (m : Mem) (B : Addr)
    (g : Reg → BitVec 64) : Saved B g l (saveMem m B g l) := by
  induction l generalizing m with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · -- The later saves are to other slots.
      have hd : ∀ q ∈ l, q.2 ≠ d := fun q hq e =>
        (List.nodup_cons.mp hf.2).1 (List.mem_map.mpr ⟨q, hq, e⟩)
      have bound : ∀ q ∈ l, q.2 % 8 = 0 ∧ q.2 < 32768 := hf.tail.1
      have hd₀ := hf.1 (r, d) List.mem_cons_self
      suffices h : ∀ (l : List (Reg × Nat)) (m : Mem), (∀ q ∈ l, q.2 ≠ d) →
          (∀ q ∈ l, q.2 % 8 = 0 ∧ q.2 < 32768) →
          (saveMem m B g l).readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 by
        rw [saveMem, h l _ hd bound, Mem.readW_writeW_self64]
      intro l
      induction l with
      | nil => intro m _ _; rfl
      | cons q l ih' =>
        intro m hne hb
        obtain ⟨r', e⟩ := q
        have he := hb (r', e) List.mem_cons_self
        have hne' := hne (r', e) List.mem_cons_self
        rw [saveMem, ih' _ (fun q hq => hne q (List.mem_cons_of_mem _ hq))
          (fun q hq => hb q (List.mem_cons_of_mem _ hq)),
          Mem.readW_writeW_sep (Offset.sep B (by dsimp only at hne' ⊢; omega) (by omega) (by omega))
            (by decide)]
    · exact ih hf.tail _ q hq

/-- The saves write only the slots, within `[B + lo, B + lo + n)`. -/
theorem saveMem_frame {l : List (Reg × Nat)} {lo n : Nat} (hl : ∀ p ∈ l, lo ≤ p.2 ∧ p.2 + 8 ≤ lo + n)
    (hn : lo + n < 2 ^ 64) (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    Frame [⟨B + BitVec.ofNat 64 lo, n⟩] m (saveMem m B g l) := by
  suffices h : ∀ m', Frame [⟨B + BitVec.ofNat 64 lo, n⟩] m m' →
      Frame [⟨B + BitVec.ofNat 64 lo, n⟩] m (saveMem m' B g l) from h m (Frame.refl _ _)
  induction l with
  | nil => exact fun _ h => h
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    intro m' h
    have hd := hl (r, d) List.mem_cons_self
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
      (h.writeW (List.mem_singleton_self _) _ (Offset.contains B hd.1 (by omega) hn))

/-- The saves write only the slots, within `[B, B + n)`. -/
theorem saveMem_frame_base {l : List (Reg × Nat)} {n : Nat} (hl : ∀ p ∈ l, p.2 + 8 ≤ n)
    (hn : n < 2 ^ 64) (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    Frame [⟨B, n⟩] m (saveMem m B g l) := by
  have h := saveMem_frame (lo := 0) (n := n) (fun p hp => ⟨Nat.zero_le _, by
    have := hl p hp; omega⟩) (by omega) m B g
  rwa [show B + BitVec.ofNat 64 0 = B from BitVec.add_zero B] at h

theorem Saved.sub {B : Addr} {g : Reg → BitVec 64} {l l' : List (Reg × Nat)} {m : Mem}
    (h : Saved B g l m) (hs : ∀ p ∈ l', p ∈ l) : Saved B g l' m :=
  fun p hp => h p (hs p hp)

/-- Writes outside the slots keep them. -/
theorem Saved.frame {B : Addr} {g : Reg → BitVec 64} {l : List (Reg × Nat)} {m m' : Mem}
    (h : Saved B g l m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ p ∈ l, ∀ r ∈ rs, Region.Disjoint ⟨B + BitVec.ofNat 64 p.2, 8⟩ r) : Saved B g l m' :=
  fun p hp => by
    rw [hf.readW (Region.contains_self _ _) (hd p hp) (by decide)]
    exact h p hp

/-- Writes outside an area holding the slots, `[B + lo, B + lo + n)`, keep them. -/
theorem Saved.frame_in {B : Addr} {g : Reg → BitVec 64} {l : List (Reg × Nat)} {m m' : Mem}
    (h : Saved B g l m) {lo n : Nat} (hl : ∀ p ∈ l, lo ≤ p.2 ∧ p.2 + 8 ≤ lo + n) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r) :
    Saved B g l m' :=
  h.frame hf fun p hp r hr => (hd r hr).sub_left (Offset.sub B (hl p hp).1 (hl p hp).2)

/-! ## Saving -/

/-- Saving the registers of `l` at the base register `b`: the state is `s`
with the saved slots. -/
theorem save_ok {b : Reg} {l : List (Reg × Nat)} {rest : List Instr} {s : State}
    {Q : State → Prop} (ho : ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 < 32768)
    (hin : ∀ p ∈ l, InRegions s.wr (s.gpr b + BitVec.ofNat 64 p.2) 8)
    (k : WP isa (.block rest) { s with mem := saveMem s.mem (s.gpr b) s.gpr l } Q) :
    WP isa (.block (saveCode b l ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k
  | cons p l ih =>
    obtain ⟨r, d⟩ := p
    rw [saveMem] at k
    rw [saveCode, List.map_cons, List.cons_append]
    have e : exec (.str .x r b d) s =
        some { s with mem := s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr r) } :=
      exec_str_x (ho (r, d) List.mem_cons_self) (hin (r, d) List.mem_cons_self)
    exact WP.block_cons_iff.mpr ⟨_, e,
      ih (fun q hq => ho q (List.mem_cons_of_mem _ hq)) (fun q hq => hin q (List.mem_cons_of_mem _ hq)) k⟩

/-- `s'` is `s` with memory `m`. -/
structure Stored (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  v : s'.v = s.v
  mem : s'.mem = m

/-- `save_ok`, as a postcondition. -/
theorem save_wp {b : Reg} {l : List (Reg × Nat)} {s : State} (ho : ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 < 32768)
    (hin : ∀ p ∈ l, InRegions s.wr (s.gpr b + BitVec.ofNat 64 p.2) 8) :
    WP isa (.block (saveCode b l)) s fun s' => Stored s s' (saveMem s.mem (s.gpr b) s.gpr l) := by
  rw [← List.append_nil (saveCode b l)]
  exact save_ok ho hin (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! ## Restoring -/

/-- After the restores of `l` from slots holding `g`: the registers of `l`
hold `g`, and nothing else changed (but the registers' own flags, which a
load does not touch either). -/
structure Restored (g : Reg → BitVec 64) (l : List (Reg × Nat)) (s s' : State) : Prop where
  gpr : ∀ p ∈ l, s'.gpr p.1 = g p.1
  other : ∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  v : s'.v = s.v

/-- A register holds `g` after the restores if it is restored or held it before. -/
theorem Restored.gpr_of {g : Reg → BitVec 64} {l : List (Reg × Nat)} {s s' : State}
    (h : Restored g l s s') {r : Reg} (hr : r ∈ l.map Prod.fst ∨ s.gpr r = g r) : s'.gpr r = g r := by
  by_cases hm : r ∈ l.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    exact h.gpr p hp
  · rw [h.other r hm]; exact hr.resolve_left hm

/-- The restores of a list with the same pairs (in another order). -/
theorem Restored.perm {g : Reg → BitVec 64} {l l' : List (Reg × Nat)} {s s' : State}
    (h : Restored g l s s') (h₁ : ∀ p ∈ l', p ∈ l) (h₂ : ∀ p ∈ l, p ∈ l') : Restored g l' s s' :=
  ⟨fun p hp => h.gpr p (h₁ p hp), fun r hr => h.other r fun hm => hr (by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm; exact List.mem_map_of_mem (h₂ p hp)),
    h.mem, h.rd, h.wr, h.sp, h.v⟩

theorem restore_wp_aux {b : Reg} {B : Addr} {g : Reg → BitVec 64} :
    ∀ {l : List (Reg × Nat)} {s : State}, (l ≠ [] → s.gpr b = B) →
    (∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 < 32768) → Restorable b l →
    (∀ p ∈ l, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 p.2) 8) → Saved B g l s.mem →
    WP isa (.block (restoreCode b l)) s (Restored g l s)
  | [], s, _, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  | (r, d) :: l, s, hb, ho, hr, hin, hsv => by
    have hd := ho _ List.mem_cons_self
    have hB := hb (List.cons_ne_nil _ _)
    have hnd := List.nodup_cons.mp hr.1
    have hrl : r ∉ l.map Prod.fst := hnd.1
    let s₁ := s.write .x r (g r)
    have e : exec (.ldr .x r b d) s = some s₁ := by
      rw [exec_ldr_x hd (by rw [hB]; exact hin _ List.mem_cons_self), hB, hsv _ List.mem_cons_self]
    have hb₁ : l ≠ [] → s₁.gpr b = B := fun hl => by
      have hrb : r ≠ b := hr.2 (r, d) (by
        rw [List.dropLast_cons_of_ne_nil hl]; exact List.mem_cons_self)
      rw [gpr_write_of_ne _ _ _ (Ne.symm hrb), hB]
    have hr₁ : Restorable b l := ⟨hnd.2, fun p hp => by
      refine hr.2 p ?_
      cases l with
      | nil => exact absurd hp List.not_mem_nil
      | cons q l => rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]; exact List.mem_cons_of_mem _ hp⟩
    rw [restoreCode, List.map_cons]
    refine WP.block_cons_iff.mpr ⟨s₁, e, WP.mono (restore_wp_aux hb₁
      (fun p hp => ho p (List.mem_cons_of_mem _ hp)) hr₁
      (fun p hp => hin p (List.mem_cons_of_mem _ hp)) (fun p hp => hsv p (List.mem_cons_of_mem _ hp)))
      fun s' h => ⟨fun p hp => ?_, fun x hx => ?_, h.mem, h.rd, h.wr, h.sp, h.v⟩⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · rw [h.other _ hrl]; exact gpr_write_self _ _ _ _
      · exact h.gpr p hp
    · simp only [List.map_cons, List.mem_cons, not_or] at hx
      rw [h.other _ hx.2]; exact gpr_write_of_ne _ _ _ hx.1

/-- Restoring the registers of `l` from the slots at the base register `b`
(which `l` may restore last). -/
theorem restore_wp {b : Reg} {l : List (Reg × Nat)} {s : State} {B : Addr} (hb : s.gpr b = B)
    (ho : ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 < 32768) (hr : Restorable b l)
    (hin : ∀ p ∈ l, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 p.2) 8)
    {g : Reg → BitVec 64} (hsv : Saved B g l s.mem) :
    WP isa (.block (restoreCode b l)) s (Restored g l s) :=
  restore_wp_aux (fun _ => hb) ho hr hin hsv

/-- `restore_wp`, followed by more code. -/
theorem restore_ok {b : Reg} {l : List (Reg × Nat)} {rest : List Instr} {s : State} {B : Addr}
    {Q : State → Prop} (hb : s.gpr b = B) (ho : ∀ p ∈ l, p.2 % 8 = 0 ∧ p.2 < 32768)
    (hr : Restorable b l) (hin : ∀ p ∈ l, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 p.2) 8)
    {g : Reg → BitVec 64} (hsv : Saved B g l s.mem)
    (k : ∀ s', Restored g l s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (restoreCode b l ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono (restore_wp hb ho hr hin hsv) k)

end VG.AArch64.Spill
