import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream

/-! # The 72-byte H₀, column and lane input to memory initialization -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
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
  input : t.gpr .rdi = s.gpr .rbp
  inputLength : t.gpr .rsi = 72
  output : t.gpr .rdx = s.gpr .r14
  outputLength : t.gpr .rcx = 1024
  work : t.gpr .r8 = s.gpr .rbx
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 →
    t.gpr r = s.gpr r
  mem : t.mem = blockMem s.mem (s.gpr .rbp) column (s.gpr .r12)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem blockArgs_ok (s : State) (column : Nat)
    (colWrite : InRegions s.wr (s.gpr .rbp + 64) 4)
    (laneWrite : InRegions s.wr (s.gpr .rbp + 68) 4) :
    WP isa (.block (blockArgs column)) s (fun t => BlockArgs s t column) := by
  apply WP.of_runBlock
  simp only [blockArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.setReg32, State.store32, HPrime.ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 64 = (64 : Addr) from rfl,
    show BitVec.ofNat 64 68 = (68 : Addr) from rfl,
    reduceCtorEq, ite_true, ite_false, colWrite, laneWrite,
    Option.map_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, h5, h6, ite_false]

end VG.Proof.Argon2.X86_64.MemoryInit
