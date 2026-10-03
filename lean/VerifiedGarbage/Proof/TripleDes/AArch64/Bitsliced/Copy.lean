import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Batch

/-!
# Copying words

`copy_ok`: the loop `copy` copies `n ≥ 1` words from `A` (in `x11`) to `B`
(in `x12`), where the two areas do not overlap, and changes nothing else in
memory. `x13` counts the words left, and `x10` holds each word.
-/

namespace VG.Proof.TripleDes.AArch64.BitslicedNeon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64.BitsliceNeon
open VG.Proof.TripleDes.Bitslice (wAt)

structure CopyPre (A B : Addr) (n : Nat) (s : State) : Prop where
  read : ∀ i < n, InRegions (s.rd ++ s.wr) (wAt A i) 8
  write : ∀ i < n, InRegions s.wr (wAt B i) 8
  sep : (⟨A, 8 * n⟩ : Region).Disjoint ⟨B, 8 * n⟩
  fitA : 8 * n < 2 ^ 64

theorem wAt_succ (p : Addr) (i : Nat) : wAt p i + BitVec.ofNat 64 8 = wAt p (i + 1) := by
  simp only [wAt, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2

/-- The registers the copy changes. -/
def CopyRegs (r : Reg) : Prop := r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13

structure CopyInv (A B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  le : i < n
  src : s.gpr .x11 = wAt A i
  dst : s.gpr .x12 = wAt B i
  cnt : s.gpr .x13 = BitVec.ofNat 64 (n - i)
  copied : ∀ j < i, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

structure CopyPost (A B : Addr) (n : Nat) (s₀ s : State) : Prop where
  copied : ∀ j < n, s.mem.readW (wAt B j) 64 = s₀.mem.readW (wAt A j) 64
  frame : Frame [⟨B, 8 * n⟩] s₀.mem s.mem
  regs : ∀ r, CopyRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : s.v = s₀.v

theorem wAt_in {p : Addr} {i n : Nat} (hi : i < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (wAt p i) 8 :=
  Offset.contains_base p (by omega) (by omega)

theorem add_ofNat_zero (a : Addr) : a + BitVec.ofNat 64 0 = a := by simp

theorem copy_ok {A B : Addr} {n : Nat} {s₀ : State} (hpre : CopyPre A B n s₀) (s : State) (i : Nat)
    (hs : CopyInv A B n s₀ i s) : WP isa copy s (CopyPost A B n s₀) := by
  refine WP.loop (M := isa) (fun m s => CopyInv A B n s₀ (n - m) s ∧ m ≤ n) ?_ (n - i) s
    ⟨by rw [show n - (n - i) = i by have := hs.le; omega]; exact hs, by omega⟩
  intro m s ⟨inv, hm⟩
  let j := n - m
  have hj : j < n := inv.le
  let v := s₀.mem.readW (wAt A j) 64
  have hv : s.mem.readW (wAt A j) 64 = v :=
    inv.frame.readW (wAt_in hj hpre.fitA) (by simpa using hpre.sep) (by decide)
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x11 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero, inv.src, inv.rd, inv.wr]; exact hpre.read j hj
  let s₁ := s.write .x .x10 v
  have e₁ : exec (.ldr .x .x10 .x11 0) s = some s₁ := by
    rw [exec_ldr_x ⟨by decide, by decide⟩ hr, add_ofNat_zero, inv.src, hv]
  have hw : InRegions s₁.wr (s₁.gpr .x12 + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero]
    have : (s.write .x .x10 v).gpr .x12 = s.gpr .x12 := by simp [State.write]
    show InRegions s.wr ((s.write .x .x10 v).gpr .x12) 8
    rw [this, inv.dst, inv.wr]; exact hpre.write j hj
  let s₂ : State := { s₁ with mem := s₁.mem.writeW (wAt B j) v }
  have e₂ : exec (.str .x .x10 .x12 0) s₁ = some s₂ := by
    rw [exec_str_x ⟨by decide, by decide⟩ hw, add_ofNat_zero]
    have h12 : s₁.gpr .x12 = wAt B j := by
      show (s.write .x .x10 v).gpr .x12 = _; simp [State.write, inv.dst]; rfl
    have h10 : s₁.gpr .x10 = v := by show (s.write .x .x10 v).gpr .x10 = _; simp [State.write]
    rw [h12, h10]
  let s₃ := s₂.write .x .x11 (s₂.read .x .x11 + BitVec.ofNat _ 8)
  let s₄ := s₃.write .x .x12 (s₃.read .x .x12 + BitVec.ofNat _ 8)
  let s₅ := s₄.write .x .x13 (s₄.read .x .x13 - BitVec.ofNat _ 1)
  have run : runBlock isa [.ldr .x .x10 .x11 0, .str .x .x10 .x12 0, .addImm .x .x11 .x11 8,
      .addImm .x .x12 .x12 8, .subImm .x .x13 .x13 1] s = some s₅ := by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₅, run, ?_⟩
  have g₅ : ∀ r, CopyRegs r → s₅.gpr r = s.gpr r := by
    intro r ⟨h1, h2, h3, h4⟩
    simp [s₅, s₄, s₃, s₂, s₁, State.write, h1, h2, h3, h4]
  have src₅ : s₅.gpr .x11 = wAt A (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.src]
    exact wAt_succ A j
  have dst₅ : s₅.gpr .x12 = wAt B (j + 1) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read, inv.dst]
    exact wAt_succ B j
  have cnt₅ : s₅.gpr .x13 = s.gpr .x13 - 1 := by
    simp [s₅, s₄, s₃, s₂, s₁, State.write, State.read]
  have mem₅ : s₅.mem = s.mem.writeW (wAt B j) v := rfl
  have copied₅ : ∀ x < j + 1, s₅.mem.readW (wAt B x) 64 = s₀.mem.readW (wAt A x) 64 := by
    intro x hx
    rw [mem₅]
    have fit := hpre.fitA
    by_cases he : x = j
    · subst he; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide)]
      exact inv.copied x (by omega)
  have frame₅ : Frame [⟨B, 8 * n⟩] s₀.mem s₅.mem := by
    rw [mem₅]; exact inv.frame.writeW List.mem_cons_self _ (wAt_in hj hpre.fitA)
  have regs₅ : ∀ r, CopyRegs r → s₅.gpr r = s₀.gpr r := fun r hr => (g₅ r hr).trans (inv.regs r hr)
  have cntv : s₅.gpr .x13 = BitVec.ofNat 64 (m - 1) := by
    rw [cnt₅, inv.cnt, show n - j = m by omega]
    exact cnt_sub m (by omega)
  have flag : isa.eval (.nonzero .x .x13) s₅ = some (m - 1 != 0) := by
    show some (s₅.read .x .x13 != 0) = _
    have hlt : m - 1 < 2 ^ 64 := by have := hpre.fitA; omega
    simp only [State.read, BitVec.setWidth_eq, cntv]
    congr 1
    by_cases h0 : m - 1 = 0
    · simp [h0]
    · have hne : BitVec.ofNat 64 (m - 1) ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this; simp at this; omega
      change (BitVec.ofNat 64 (m - 1) != (0 : BitVec 64)) = (m - 1 != 0)
      simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]
  by_cases h1 : m = 1
  · left
    refine ⟨by rw [flag, h1]; rfl, ?_⟩
    exact ⟨fun x hx => copied₅ x (by omega), frame₅, regs₅, inv.rd, inv.wr, inv.sp, inv.v⟩
  · right
    refine ⟨by rw [flag]; simp; omega, m - 1, by omega, ⟨?_, ?_, ?_, ?_, ?_, frame₅, regs₅, inv.rd,
      inv.wr, inv.sp, inv.v⟩, by omega⟩
    · omega
    · rw [src₅]; congr 2; omega
    · rw [dst₅]; congr 2; omega
    · rw [cntv]; congr 1; omega
    · intro x hx; exact copied₅ x (by omega)

end VG.Proof.TripleDes.AArch64.BitslicedNeon
