import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (16 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`); and the registers `absorb` saves at `scratch + 2176`, where the
functions it calls do not write, and restores at the end.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (readW_writeW_other)
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega

/-! ## Arithmetic on registers -/

theorem shr_ofNat {n k : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega)]

/-- The sign of `m - k`, for `m` and `k` of at most 16. -/
theorem lsr63 {m k : Nat} (hm : m ≤ 16) (hk : k ≤ 16) :
    (BitVec.ofNat 64 m - BitVec.ofNat 64 k) >>> 63 = BitVec.ofNat 64 (if m < k then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- `16 nb` for the data left `x > 0`, as `sub 1; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 1 - ((BitVec.ofNat 64 x - BitVec.ofNat 64 1) &&& 15) =
      BitVec.ofNat 64 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 64 x - BitVec.ofNat 64 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega

/-! ## Saving and restoring the registers -/

/-- The memory after saving the registers at `S + 2176`. -/
abbrev absSavedMem (s : State) (S : Addr) : Mem := Spill.saveMem s.mem S s.gpr saved

/-- Each slot holds the register saved there. -/
theorem absSaved_slot (s : State) (S : Addr) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (absSavedMem s S).readW (S + BitVec.ofNat 64 d) 64 = s.gpr r :=
  Spill.saveMem_saved (l := saved) (by decide) s.mem S s.gpr (r, d) h

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 56⟩] s.mem (absSavedMem s S) :=
  Spill.saveMem_frame (by decide) (by decide) _ _ _

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .x5 = S)
    (hw : ∀ d, 2176 ≤ d → d + 8 ≤ 2232 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧ s'.gpr .x21 = s.gpr .x3 ∧
      s'.gpr .x22 = s.gpr .x4 ∧ s'.gpr .x23 = S ∧ s'.gpr .x2 = s.gpr .x2 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [← hS] at hw ⊢
  refine ⟨_, by
    simp (config := {decide := true}) only [save, saved, mov, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some,
      hw 2176 (by decide) (by decide), hw 2184 (by decide) (by decide), hw 2192 (by decide) (by decide),
      hw 2200 (by decide) (by decide), hw 2208 (by decide) (by decide), hw 2216 (by decide) (by decide),
      hw 2224 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ => ?_, rfl, ?_, rfl, rfl⟩
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅]
  · simp only [mem_write, absSavedMem, saved, Spill.saveMem, Mem.writeW, BitVec.setWidth_eq]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .x23 = B)
    (hr : ∀ d, 2176 ≤ d → d + 8 ≤ 2232 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ r d, (r, d) ∈ saved → s'.gpr r = s.mem.readW (B + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x24 → r ≠ .x30 → r ≠ .x23 →
        s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, hb,
      hr 2176 (by decide) (by decide), hr 2184 (by decide) (by decide), hr 2192 (by decide) (by decide),
      hr 2200 (by decide) (by decide), hr 2208 (by decide) (by decide), hr 2216 (by decide) (by decide),
      hr 2224 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨fun r d h => ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [gpr_write, Mem.readW]
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64) (hd : s.gpr .x2 = BitVec.ofNat 64 c) :
    WP isa held s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (held c) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [eval_zero hc hd]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ite_true]
      rfl, ?_⟩
    exact ⟨by simp [gpr_write]; rfl, fun r h _ => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
  · have hne : BitVec.ofNat 64 c ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [toNat_ofNat hc] at this)
    refine WP.ite false (by rw [eval_zero hc hd]; simp [h0]) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ite_true, ite_false, BitVec.setWidth_eq, mz15, hd, reduceCtorEq]
    rw [held_bv _ hne, toNat_ofNat hc]

/-! ## `fill`: how many bytes to copy, and where -/

theorem clamp_wp {s : State} {L : Nat} (hL : L < 2 ^ 64) (h22 : s.gpr .x22 = BitVec.ofNat 64 L) :
    WP isa clamp s fun s' => s'.gpr .x10 = BitVec.ofNat 64 (min L 16) ∧
      (∀ r, r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x10₁, g₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x10 .x22 4] s = some s₁ ∧
      s₁.gpr .x10 = BitVec.ofNat 64 (L / 16) ∧ s₁ = s.write .x .x10 (BitVec.ofNat 64 (L / 16)) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, ite_true, BitVec.setWidth_eq, h22, shr_ofNat hL], by simp [gpr_write], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ev := eval_zero (s := s₁) (x := L / 16) (by omega) x10₁
  subst g₁
  by_cases hl : L < 16
  · refine WP.ite true (by rw [ev]; simp; omega) (fun _ => ?_) (fun h => by cases h)
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, h22, Nat.min_eq_left (Nat.le_of_lt hl)]
  · refine WP.ite false (by rw [ev]; simp; omega) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ite_true]
      rfl, ?_⟩
    refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    simp only [gpr_write, ite_true, BitVec.setWidth_eq, mz16, Nat.min_eq_right (Nat.le_of_not_lt hl)]

theorem fill_wp {s : State} {St D : Addr} {c L : Nat} (hL : L < 2 ^ 64)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (held c)) (h22 : s.gpr .x22 = BitVec.ofNat 64 L)
    (h19 : s.gpr .x19 = St) (h21 : s.gpr .x21 = D) :
    WP isa fill s fun s' => s'.gpr .x8 = BitVec.ofNat 64 (fOf c L) ∧
      s'.gpr .x10 = BitVec.ofNat 64 (fOf c L) ∧ s'.gpr .x6 = St + BitVec.ofNat 64 (288 + held c) ∧
      s'.gpr .x7 = D ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hh := held_le c
  refine WP.seq (WP.mono (clamp_wp hL h22) fun s₁ ⟨x10₁, g₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain ⟨s₂, run₂, x8₂, x10₂, x11₂, g₂, sp₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.movz .x .x8 16 0,
      .sub .x .x8 .x8 .x9, .sub .x .x11 .x10 .x8, .lsr .x .x11 .x11 63] s₁ = some s₂ ∧
      s₂.gpr .x8 = BitVec.ofNat 64 (16 - held c) ∧ s₂.gpr .x10 = BitVec.ofNat 64 (min L 16) ∧
      s₂.gpr .x11 = BitVec.ofNat 64 (if min L 16 < 16 - held c then 1 else 0) ∧
      (∀ r, r ≠ .x8 → r ≠ .x11 → s₂.gpr r = s₁.gpr r) ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    have x9₁ : s₁.gpr .x9 = BitVec.ofNat 64 (held c) := by rw [g₁ _ (by decide), h9]
    refine ⟨?_, ?_, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, mz16, x9₁,
        Offset.ofNat_sub_ofNat hh]
    · simp only [gpr_write, ite_false, reduceCtorEq, x10₁]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, mz16, x9₁, x10₁,
        Offset.ofNat_sub_ofNat hh]
      exact lsr63 (by omega) (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hf : fOf c L = min (min L 16) (16 - held c) := by unfold fOf; omega
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .x8 = BitVec.ofNat 64 (fOf c L) ∧
    (∀ r, r ≠ .x8 → s₃.gpr r = s₂.gpr r) ∧ s₃.sp = s₂.sp ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧
      s₃.wr = s₂.wr) ?_ fun s₃ h₃ => ?_)
  · have ev := eval_zero (s := s₂) (x := if min L 16 < 16 - held c then 1 else 0) (by split <;> omega) x11₂
    by_cases hl : min L 16 < 16 - held c
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
          Size.bits, State.read, ite_true, BitVec.setWidth_eq]
        rfl, ?_⟩
      refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, x10₂, hf,
        Nat.min_eq_left (Nat.le_of_lt hl)]
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x8₂, hf, Nat.min_eq_right (Nat.le_of_not_lt hl)], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨x8₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := h₃
    have g (r : Reg) (a : r ≠ .x8) (b : r ≠ .x11) (d : r ≠ .x10) : s₃.gpr r = s.gpr r := by
      rw [g₃ r a, g₂ r a b, g₁ r d]
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, fun r a b d e f => ?_, by simp only [sp_write, sp₃, sp₂, sp₁],
      by simp only [mem_write, m₃, m₂, m₁], by simp only [rd_write, rd₃, rd₂, rd₁],
      by simp only [wr_write, wr₃, wr₂, wr₁]⟩
    · simp only [gpr_write, ite_false, reduceCtorEq, x8₃]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero, x8₃]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), g .x9 (by decide) (by decide) (by decide), h19, h9]
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x21 (by decide) (by decide) (by decide), h21]
    · simp only [gpr_write, a, b, e, ite_false]
      exact g r d f e

/-! ## `chain1`: the arguments of the first call -/

theorem chain1_wp {s : State} {St D S : Addr} {f L : Nat} (hf : f ≤ L) (hL : L < 2 ^ 64)
    (h21 : s.gpr .x21 = D) (h10 : s.gpr .x10 = BitVec.ofNat 64 f) (h22 : s.gpr .x22 = BitVec.ofNat 64 L)
    (h19 : s.gpr .x19 = St) (h23 : s.gpr .x23 = S) :
    WP isa chain1 s fun s' => s'.gpr .x21 = D + BitVec.ofNat 64 f ∧ s'.gpr .x22 = BitVec.ofNat 64 (L - f) ∧
      s'.gpr .x4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧ s'.gpr .x0 = St ∧
      s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = St + BitVec.ofNat 64 272 ∧
      s'.gpr .x3 = St + BitVec.ofNat 64 288 ∧ s'.gpr .x5 = S ∧
      (∀ r ∈ preserved, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x21₁, x22₁, x4₁, g₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.add .x .x21 .x21 .x10,
      .sub .x .x22 .x22 .x10, .movz .x .x4 0 0] s = some s₁ ∧
      s₁.gpr .x21 = D + BitVec.ofNat 64 f ∧ s₁.gpr .x22 = BitVec.ofNat 64 (L - f) ∧
      s₁.gpr .x4 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x21 → r ≠ .x22 → r ≠ .x4 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, fun r a b c => by simp [gpr_write, a, b, c], rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h21, h10]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h22, h10,
        Offset.ofNat_sub_ofNat hf]
    · simp only [gpr_write, ite_true, BitVec.setWidth_eq, mz0]; rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .x4 = BitVec.ofNat 64 (if L - f = 0 then 0 else 1) ∧
    (∀ r, r ≠ .x4 → s₂.gpr r = s₁.gpr r) ∧ s₂.sp = s₁.sp ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero (s := s₁) (x := L - f) (by omega) x22₁
    by_cases h0 : L - f = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x4₁]; simp [h0], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
          ite_true]
        rfl, ?_⟩
      refine ⟨?_, fun r h => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, BitVec.setWidth_eq, mz1, h0]; rfl
  · obtain ⟨x4₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := h₂
    have g (r : Reg) (a : r ≠ .x21) (b : r ≠ .x22) (c : r ≠ .x4) : s₂.gpr r = s.gpr r := by
      rw [g₂ r c, g₁ r a b c]
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, by simp only [sp_write, sp₂, sp₁],
      by simp only [mem_write, m₂, m₁], by simp only [rd_write, rd₂, rd₁], by simp only [wr_write, wr₂, wr₁]⟩
    · simp only [gpr_write, ite_false, reduceCtorEq, g₂ _ (by decide : Reg.x21 ≠ .x4), x21₁]
    · simp only [gpr_write, ite_false, reduceCtorEq, g₂ _ (by decide : Reg.x22 ≠ .x4), x22₁]
    · simp only [gpr_write, ite_false, reduceCtorEq, x4₂]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x19 (by decide) (by decide) (by decide), h19]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x20 (by decide) (by decide) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), h19]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g .x19 (by decide) (by decide) (by decide), h19]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero,
        g .x23 (by decide) (by decide) (by decide), h23]
    · have hc : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
      obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hc r hr
      simp only [gpr_write, n0, n1, n2, n3, n5, ite_false]
      exact g r a b n4

/-! ## `chain2`: the arguments of the second call -/

theorem chain2_wp {s : State} {x : Nat} (hx : x < 2 ^ 64) (h22 : s.gpr .x22 = BitVec.ofNat 64 x) :
    WP isa chain2 s fun s' =>
      s'.gpr .x24 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
      s'.gpr .x4 = BitVec.ofNat 64 (if x = 0 then 0 else (x - 1) / 16) ∧ s'.gpr .x0 = s.gpr .x19 ∧
      s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x19 + BitVec.ofNat 64 272 ∧
      s'.gpr .x3 = s.gpr .x21 ∧ s'.gpr .x5 = s.gpr .x23 ∧
      (∀ r ∈ preserved, r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x24₁, g₁⟩ : ∃ s₁, runBlock isa [.movz .x .x24 0 0] s = some s₁ ∧
      s₁.gpr .x24 = BitVec.ofNat 64 0 ∧ s₁ = s.write .x .x24 (BitVec.ofNat 64 0) := by
    refine ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        ite_true, mz0]
      rfl, by simp [gpr_write], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
    s₂.gpr .x24 = BitVec.ofNat 64 (16 * (if x = 0 then 0 else (x - 1) / 16)) ∧
    (∀ r, r ≠ .x24 → r ≠ .x9 → s₂.gpr r = s.gpr r) ∧ s₂.sp = s.sp ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr) ?_ fun s₂ h₂ => ?_)
  · have ev := eval_zero (s := s.write .x .x24 (BitVec.ofNat 64 0)) (r := .x22) (x := x) hx
      (by simp only [gpr_write, reduceCtorEq, ite_false, h22])
    by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [x24₁]; simp [h0], fun r h _ => by simp [gpr_write, h], rfl, rfl, rfl, rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine WP.of_runBlock ⟨_, by
        simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
          State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
        rfl, ?_⟩
      refine ⟨?_, fun r a b => by simp [gpr_write, a, b], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, mz15, h22, h0]
      exact nb16_bv (by omega) hx
  · obtain ⟨x24₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := h₂
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr a => ?_, by simp only [sp_write, sp₂],
      by simp only [mem_write, m₂], by simp only [rd_write, rd₂], by simp only [wr_write, wr₂]⟩
    · simp only [gpr_write, ite_false, reduceCtorEq, x24₂]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, x24₂]
      exact (shr_ofNat (by split <;> omega)).trans (by congr 1; omega)
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x19 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x20 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        g₂ _ (by decide : Reg.x19 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x21 ≠ .x24) (by decide)]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq,
        BitVec.add_zero, g₂ _ (by decide : Reg.x23 ≠ .x24) (by decide)]
    · have hc : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x9 := by
        decide
      obtain ⟨n0, n1, n2, n3, n4, n5, n9⟩ := hc r hr
      simp only [gpr_write, n0, n1, n2, n3, n4, n5, ite_false]
      exact g₂ r a n9

/-! ## `rest`: the arguments of the last copy -/

theorem rest_ok {s : State} {D : Addr} {a x n : Nat} (hn : 16 * n ≤ x)
    (h21 : s.gpr .x21 = D + BitVec.ofNat 64 a) (h24 : s.gpr .x24 = BitVec.ofNat 64 (16 * n))
    (h22 : s.gpr .x22 = BitVec.ofNat 64 x) :
    ∃ s', runBlock isa rest s = some s' ∧ s'.gpr .x21 = D + BitVec.ofNat 64 (a + 16 * n) ∧
      s'.gpr .x22 = BitVec.ofNat 64 (x - 16 * n) ∧ s'.gpr .x6 = s.gpr .x19 + BitVec.ofNat 64 288 ∧
      s'.gpr .x7 = D + BitVec.ofNat 64 (a + 16 * n) ∧ s'.gpr .x8 = BitVec.ofNat 64 (x - 16 * n) ∧
      (∀ r ∈ preserved, r ≠ .x21 → r ≠ .x22 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rest, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
    rfl, ?_⟩
  have e : D + BitVec.ofNat 64 a + BitVec.ofNat 64 (16 * n) = D + BitVec.ofNat 64 (a + 16 * n) :=
    Offset.add_add _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr a b => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h21, h24, e]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h22, h24,
      Offset.ofNat_sub_ofNat hn]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero, h21, h24, e]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, BitVec.add_zero, h22, h24,
      Offset.ofNat_sub_ofNat hn]
  · have hc : ∀ r ∈ preserved, r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := by decide
    obtain ⟨n6, n7, n8⟩ := hc r hr
    simp only [gpr_write, a, b, n6, n7, n8, ite_false]

end VG.Proof.CmacAes.Stream.AArch64
