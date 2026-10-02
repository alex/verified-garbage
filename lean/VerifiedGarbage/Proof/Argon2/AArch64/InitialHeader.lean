import VerifiedGarbage.Proof.Argon2.AArch64.InitialLayout

/-! # Writing and reading the six words of the H₀ header -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def headerValue (s : State) (j : Nat) : BitVec 32 :=
  if j = 4 then 0x13 else (wordAt s (headerSource j)).setWidth 32

def headerMem (s : State) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s n).writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * n))
    (headerValue s n)

theorem headerSource_slot (j : Nat) : headerSource j ∈ slots := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerSource_bound (j : Nat) : headerSource j + 8 ≤ 272 := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerValue_keeps {s t : State} (h : Space s) (k : Keeps s t) (j : Nat) :
    headerValue t j = headerValue s j := by
  unfold headerValue
  rw [h.word_keeps k _ (headerSource_bound j)]

theorem headerMem_frame (s : State) (n : Nat) (hn : n ≤ 6) :
    Frame [⟨s.gpr .x24 + 768, 24⟩] s.mem (headerMem s n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega) (by omega))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (headerMem s n).readW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      headerValue s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem headerMem_bytes (s : State) :
    bytesAt (headerMem s 6) (s.gpr .x24 + 768) 24 =
      (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (headerValue s j)) := by
  rw [show 24 = 32 / 8 * 6 from rfl, Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl)]
  rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.add_assoc,
    ← BitVec.ofNat_add, headerMem_read s 6 j (by decide) (List.mem_range.mp hj)]

theorem headerSlot_ok (s : State) (j : Nat) (hj : j < 6) (h : Space s) :
    WP isa (.block (headerSlot j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
      Keeps s t := by
  have hw := h.write (768 + 4 * j) 4 (by omega)
  have finish (t : State) (hm : t.mem = s.mem.writeW
      (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j))
      (regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r)
      (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) :
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
        Keeps s t := by
    refine ⟨hm, fun r hr _ _ => regs r ?_, sp, rd, wr, ?_⟩
    · simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by omega) (by omega))
  unfold headerSlot
  split
  · next he =>
    subst j
    have hwLiteral : InRegions s.wr (s.gpr .x24 + 784#64) 4 := hw
    apply WP.of_runBlock
    simp only [Impl.Argon2.AArch64.Instructions.imm,
      Impl.Argon2.AArch64.Instructions.store32, show 19 < 65536 from by decide,
      List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr,
      Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT, Nat.reduceMod,
      BitVec.shiftLeft_zero, show (19#16).setWidth 64 = 19#64 from rfl,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      hwLiteral, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, and_self,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, ?_⟩
    constructor
    · intro r hr _ _
      have hn : r ≠ .x8 := by
        simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [RegUpd.gpr_write, hn, ite_false]
    · simp only [RegUpd.sp_write]
    · rfl
    · rfl
    · change Frame [⟨s.gpr .x24, 832⟩, below s.sp 16] s.mem
        (s.mem.writeW (s.gpr .x24 + 784) (19#32))
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (d := 784) (n := 4) (by decide : 784 + 4 ≤ 832) (by decide))
  · next he =>
    have align : headerSource j % 8 = 0 := by
      unfold headerSource
      split <;> (try split) <;> (try split) <;> (try split) <;> decide
    refine (headerWord_ok s _ _ align (by have := headerSource_bound j; omega)
      (by omega) (by omega) (h.readable _ (headerSource_slot j)) hw).mono ?_
    rintro t ⟨hm, regs, rd, wr, sp⟩
    exact finish t (by simpa only [headerValue, he, ite_false, wordAt] using hm) regs rd wr sp

theorem headerWords_ok (s : State) (n : Nat) (hn : n ≤ 6) (h : Space s) :
    WP isa (.block ((List.range n).flatMap headerSlot)) s fun t =>
      t.mem = headerMem s n ∧ Keeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine (ih (by omega)).mono ?_
    rintro u ⟨hu, ku⟩
    refine (headerSlot_ok u n (by omega) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.x24, headerValue_keeps h ku, hu]
    rfl

theorem header_ok (s : State) (h : Space s) :
    WP isa (.block header) s fun t =>
      bytesAt t.mem (s.gpr .x24 + 768) 24 =
        (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (headerValue s j)) ∧ Keeps s t :=
  (headerWords_ok s 6 (by decide) h).mono fun t ⟨hm, hk⟩ =>
    ⟨by rw [hm]; exact headerMem_bytes s, hk⟩

end VG.Proof.Argon2.AArch64.Initial
