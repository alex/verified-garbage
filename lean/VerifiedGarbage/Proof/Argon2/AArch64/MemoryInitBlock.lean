import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCall
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream

/-! Merged from `Proof.Argon2.AArch64.MemoryInitArgs`. -/
section
/-! # The 72-byte H₀, column and lane input to memory initialization -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

def blockMem (m : Mem) (p : Addr) (column : Nat) (lane : Addr) : Mem :=
  (m.writeW (p + 64) (BitVec.ofNat 32 column)).writeW (p + 68) (lane.setWidth 32)

theorem blockMem_frame (m : Mem) (p : Addr) (column : Nat) (lane : Addr) :
    Frame [⟨p + 64, 8⟩] m (blockMem m p column lane) := by
  unfold blockMem
  have first : Frame [⟨p + 64, 8⟩] m (m.writeW (p + 64) (BitVec.ofNat 32 column)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa only [BitVec.add_zero] using
        Offset.contains_base (p + 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide))
  apply first.writeW (List.mem_singleton_self _)
  have eq : p + 68 = (p + 64) + BitVec.ofNat 64 4 := by rw [BitVec.add_assoc]; rfl
  rw [eq]
  exact Offset.contains_base _ (by decide : 4 + 4 ≤ 8) (by decide)

theorem blockMem_bytes (m : Mem) (p : Addr) (column : Nat) (lane : Addr) :
    bytesAt (blockMem m p column lane) p 72 =
      bytesAt m p 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 lane.toNat := by
  have first : bytesAt (blockMem m p column lane) p 64 = bytesAt m p 64 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply (blockMem_frame m p column lane).bytes (R := ⟨p, 64⟩) _
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
    · intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact Offset.base_disjoint _ (by decide) (by decide)

  have columnWord : (blockMem m p column lane).readW (p + 64) 32 = BitVec.ofNat 32 column := by
    unfold blockMem
    rw [Mem.readW_writeW_sep ?_ (by decide), Mem.readW_writeW_self32]
    exact Offset.sep p (by decide) (by decide) (by decide)
  have laneWord : (blockMem m p column lane).readW (p + 68) 32 = lane.setWidth 32 :=
    Mem.readW_writeW_self32 _ _ _
  have words := Proof.Blake2.bytesAt_add (blockMem m p column lane) (p + 64) 4 4
  have pos : p + 64 + BitVec.ofNat 64 4 = p + 68 := by rw [BitVec.add_assoc]; rfl
  rw [pos, ← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl),
    ← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl), columnWord, laneWord] at words
  have header := Proof.Blake2.bytesAt_add (blockMem m p column lane) p 64 8
  change bytesAt (blockMem m p column lane) (p + 64) 8 = _ at words
  rw [show BitVec.ofNat 64 64 = (64 : Addr) from rfl, first, words, ← BitVec.ofNat_toNat 32 lane, ← List.append_assoc] at header
  exact header

structure BlockArgs (s t : State) (column : Nat) : Prop where
  input : t.gpr .x0 = s.gpr .x19
  inputLength : t.gpr .x1 = 72
  output : t.gpr .x2 = s.gpr .x22
  outputLength : t.gpr .x3 = 1024
  work : t.gpr .x4 = s.gpr .x24
  other : ∀ r, r ≠ .x8 → r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 →
    t.gpr r = s.gpr r
  mem : t.mem = blockMem s.mem (s.gpr .x19) column (s.gpr .x20)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem blockArgs_ok (s : State) (column : Nat) (columnBound : column < 65536)
    (colWrite : InRegions s.wr (s.gpr .x19 + 64) 4)
    (laneWrite : InRegions s.wr (s.gpr .x19 + 68) 4) :
    WP isa (.block (blockArgs column)) s (fun t => BlockArgs s t column) := by
  have colLiteral : InRegions s.wr (s.gpr .x19 + 64#64) 4 := colWrite
  have laneLiteral : InRegions s.wr (s.gpr .x19 + 68#64) 4 := laneWrite
  have col : (BitVec.ofNat 16 column).setWidth 64 = BitVec.ofNat 64 column :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) columnBound
  apply WP.of_runBlock
  simp only [blockArgs, Impl.Argon2.AArch64.Instructions.imm,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.store32,
    columnBound, show 72 < 65536 from by decide, show 1024 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.store, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod,
    show 0 < 4096 from by decide, BitVec.shiftLeft_zero, col,
    show (72#16).setWidth 64 = 72#64 from rfl,
    show (1024#16).setWidth 64 = 1024#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    reduceCtorEq, ite_true, ite_false, colLiteral, laneLiteral, and_self,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.add_zero,
    BitVec.setWidth_eq]
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  · intro r h1 h2 h3 h4 h5 h6
    simp only [RegUpd.gpr_write, h1, h2, h3, h4, h5, h6, ite_false]
  · simp only [RegUpd.mem_write, blockMem, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64)]
    rfl
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Initializing a block while preserving H₀ and the public lane counters -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure BlockReady (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  input : Covers [⟨s.gpr .x19, 72⟩] s.wr
  output : Covers [⟨s.gpr .x22, 1024⟩] s.wr
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  frameWork : (⟨s.gpr .x19, 72⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  frameOutput : (⟨s.gpr .x19, 72⟩ : Region).Disjoint ⟨s.gpr .x22, 1024⟩
  outputWork : (⟨s.gpr .x22, 1024⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackFrame : (below (s.sp) 16).Disjoint ⟨s.gpr .x19, 72⟩
  stackOutput : (below (s.sp) 16).Disjoint ⟨s.gpr .x22, 1024⟩
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩

theorem BlockArgs.regs {s t : State} {column : Nat} (h : BlockArgs s t column)
    (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have hn : r ≠ .x8 ∧ r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem BlockReady.prefix {s : State} (h : BlockReady s) (d : Nat)
    (bound : d + 4 ≤ 72) : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 4 := by
  exact h.input _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem BlockArgs.ready {s t : State} {column : Nat} (a : BlockArgs s t column)
    (h : BlockReady s) : CallReady t := by
  have base := a.regs .x24 (by decide)
  have sp := a.sp
  refine ⟨by rw [sp]; exact h.stackMinimum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a.input, a.rd, a.wr]
    intro p n ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst r
    obtain ⟨r, hr, hc'⟩ := h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [a.output, a.wr]; exact h.output
  · rw [a.work, a.wr]; exact h.work
  · rw [a.input, a.work]; exact h.frameWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [sp, a.input]; exact h.stackFrame
  · rw [sp, a.output]; exact h.stackOutput
  · rw [sp, a.work]; exact h.stackWork

structure BlockDone (s t : State) (column : Nat) : Prop where
  digest : bytesAt t.mem (s.gpr .x22) 1024 = Spec.Argon2.hPrime 1024
    (bytesAt s.mem (s.gpr .x19) 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 (s.gpr .x20).toNat)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x22, 1024⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

theorem block_ok (v : HPrime.Backend) (name : String)
    (s : State) (column : Nat) (columnBound : column < 65536) (h : BlockReady s) :
    WP isa (block name v.hash column) s (fun t => BlockDone s t column) := by
  unfold block
  refine WP.seq ((blockArgs_ok s column columnBound
    (by simpa only [show BitVec.ofNat 64 64 = (64 : Addr) from rfl] using h.prefix 64 (by decide))
    (by simpa only [show BitVec.ofNat 64 68 = (68 : Addr) from rfl] using h.prefix 68 (by decide))).mono ?_)
  intro a ha
  refine (hPrime_call_ok v name a (ha.ready h) ha.inputLength ha.outputLength).mono ?_
  intro t ht
  refine ⟨?_, fun r hr => (ht.regs r hr).trans (ha.regs r hr),
    ht.sp.trans ha.sp, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
  · have digest := ht.digest
    rw [ha.output, ha.input, ha.mem, blockMem_bytes] at digest
    exact digest
  · have argsFrame : Frame [⟨s.gpr .x22, 1024⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem a.mem := by
      rw [ha.mem]
      exact (blockMem_frame _ _ _ _).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    apply argsFrame.trans
    have frame := ht.frame
    rw [ha.output, ha.work, ha.sp] at frame
    exact frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))

end VG.Proof.Argon2.AArch64.MemoryInit
