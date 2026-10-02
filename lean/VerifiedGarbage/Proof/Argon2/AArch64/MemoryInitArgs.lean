import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream

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
