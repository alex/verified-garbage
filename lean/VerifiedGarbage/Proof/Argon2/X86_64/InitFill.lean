import VerifiedGarbage.Impl.Argon2.X86_64.InitFill
import VerifiedGarbage.Proof.Argon2.X86_64.FillFinish
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillIterationsBody
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Argon2.X86_64.FillSetup
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitCall
import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitScale
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLayout
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSteps
import VerifiedGarbage.Proof.Argon2.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitClear
import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.Blake2.Stream

/-! Merged from `Proof.Argon2.X86_64.MemoryInitBlock`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitArgs`. -/
section
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
end

/-! # Initializing a block while preserving H₀ and the public lane counters -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure BlockReady (s : State) : Prop where
  input : Covers [⟨s.gpr .rbp, 72⟩] s.wr
  output : Covers [⟨s.gpr .r14, 1024⟩] s.wr
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  frameWork : (⟨s.gpr .rbp, 72⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  frameOutput : (⟨s.gpr .rbp, 72⟩ : Region).Disjoint ⟨s.gpr .r14, 1024⟩
  outputWork : (⟨s.gpr .r14, 1024⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackFrame : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbp, 72⟩
  stackOutput : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .r14, 1024⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbx, 16384⟩

theorem BlockArgs.regs {s t : State} {column : Nat} (h : BlockArgs s t column)
    (r : Reg) (hr : r ∈ calleeSaved) : t.gpr r = s.gpr r := by
  have hn : r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r8 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem BlockReady.prefix {s : State} (h : BlockReady s) (d : Nat)
    (bound : d + 4 ≤ 72) : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 4 := by
  exact h.input _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem BlockArgs.ready {s t : State} {column : Nat} (a : BlockArgs s t column)
    (h : BlockReady s) : CallReady t := by
  have base := a.regs .rbx (by decide)
  have sp := a.regs .rsp (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  digest : bytesAt t.mem (s.gpr .r14) 1024 = Spec.Argon2.hPrime 1024
    (bytesAt s.mem (s.gpr .rbp) 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 (s.gpr .r12).toNat)
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .r14, 1024⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem block_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (column : Nat) (h : BlockReady s) :
    WP isa (block name (HPrime.hash v) column) s (fun t => BlockDone s t column) := by
  unfold block
  refine WP.seq ((blockArgs_ok s column
    (by simpa only [show BitVec.ofNat 64 64 = (64 : Addr) from rfl] using h.prefix 64 (by decide))
    (by simpa only [show BitVec.ofNat 64 68 = (68 : Addr) from rfl] using h.prefix 68 (by decide))).mono ?_)
  intro a ha
  refine (hPrime_call_ok v name a (ha.ready h) ha.inputLength ha.outputLength).mono ?_
  intro t ht
  refine ⟨?_, fun r hr => (ht.regs r hr).trans (ha.regs r hr),
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
  · have digest := ht.digest
    rw [ha.output, ha.input, ha.mem, blockMem_bytes] at digest
    exact digest
  · have argsFrame : Frame [⟨s.gpr .r14, 1024⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem a.mem := by
      rw [ha.mem]
      exact (blockMem_frame _ _ _ _).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    apply argsFrame.trans
    have frame := ht.frame
    rw [ha.output, ha.work, ha.regs .rsp (by decide)] at frame
    exact frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitSpace`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitMatrix`. -/
section
/-! # Matrix cells and the memory preserved by initialization calls -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

theorem clearMem_block (m : Mem) (p : Addr) (blocks k : Nat)
    (bound : 1024 * blocks < 2 ^ 64) (hk : k < blocks) :
    blockAt (clearMem m p (128 * blocks)) (p + BitVec.ofNat 64 (1024 * k)) = zeroBlock := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, zeroBlock, Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 1024 * k + 8 * j = 8 * (128 * k + j) by omega]
  exact clearMem_word m p (128 * blocks) (128 * k + j) (by omega) (by omega)

theorem blockAt_frame {m m' : Mem} {rs : List Region} (frame : Frame rs m m')
    (p : Addr) (sep : ∀ r ∈ rs, (⟨p, 1024⟩ : Region).Disjoint r) :
    blockAt m' p = blockAt m p := by
  rw [← Proof.Argon2.parseBlock_bytesAt, ← Proof.Argon2.parseBlock_bytesAt]
  apply congrArg parseBlock
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  exact frame.bytes (R := ⟨p, 1024⟩) sep (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi

theorem BlockDone.h0 {s t : State} {column : Nat} (h : BlockDone s t column)
    (ready : BlockReady s) : bytesAt t.mem (s.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .rbp, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ready.frameOutput.sub_left (Region.sub_prefix (by decide))
  · exact ready.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact ready.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem BlockDone.block {s t : State} {column : Nat} (h : BlockDone s t column) :
    blockAt t.mem (s.gpr .r14) = parseBlock
      (Proof.Argon2.initialBytes (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat column) :=
  Proof.Argon2.blockAt_of_initialBytes _ _ _ _ _ h.digest

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Permissions for the matrix, derivation frame and hash scratch -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Space (s : State) (memory : Addr) (bytes : Nat) : Prop where
  matrix : Covers [⟨memory, bytes⟩] s.wr
  frame : Covers [⟨s.gpr .rbp, 72⟩] s.wr
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  frameMatrix : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨memory, bytes⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  matrixWork : (⟨memory, bytes⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackFrame : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbp, 272⟩
  stackMatrix : (below (s.gpr .rsp) 24).Disjoint ⟨memory, bytes⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbx, 16384⟩
  bound : bytes < 2 ^ 64

theorem Space.same {s t : State} {memory : Addr} {bytes : Nat} (h : Space s memory bytes)
    (wr : t.wr = s.wr) (bp : t.gpr .rbp = s.gpr .rbp)
    (bx : t.gpr .rbx = s.gpr .rbx) (sp : t.gpr .rsp = s.gpr .rsp) : Space t memory bytes := by
  constructor
  · rw [wr]; exact h.matrix
  · rw [bp, wr]; exact h.frame
  · rw [bx, wr]; exact h.work
  · rw [bp]; exact h.frameMatrix
  · rw [bp, bx]; exact h.frameWork
  · rw [bx]; exact h.matrixWork
  · rw [sp, bp]; exact h.stackFrame
  · rw [sp]; exact h.stackMatrix
  · rw [sp, bx]; exact h.stackWork
  · exact h.bound

theorem Space.blockReady {s : State} {memory : Addr} {bytes d : Nat}
    (h : Space s memory bytes) (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d)
    (bound : d + 1024 ≤ bytes) : BlockReady s := by
  have outputSub : Region.Sub ⟨s.gpr .r14, 1024⟩ ⟨memory, bytes⟩ := by
    rw [dst]; exact Offset.sub_base _ bound
  have outputCover : Covers [⟨s.gpr .r14, 1024⟩] s.wr := by
    have narrow : Covers [⟨s.gpr .r14, 1024⟩] [⟨memory, bytes⟩] := Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, d, dst, bound⟩)
    exact fun p n hp => h.matrix p n (narrow p n hp)
  exact ⟨h.frame, outputCover, h.work,
    h.frameWork.sub_left (Region.sub_prefix (by decide)),
    (h.frameMatrix.sub_left (Region.sub_prefix (by decide))).sub_right outputSub,
    h.matrixWork.sub_left outputSub,
    h.stackFrame.sub_right (Region.sub_prefix (by decide)),
    h.stackMatrix.sub_right outputSub, h.stackWork⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitLane`. -/
section
/-! # Initializing both leading blocks of one lane -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LaneDone (s t : State) : Prop where
  first : bytesAt t.mem (s.gpr .r14) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat 0
  second : bytesAt t.mem (s.gpr .r14 + 1024) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat 1
  destination : t.gpr .r14 = s.gpr .r14 + s.gpr .r13
  lane : t.gpr .r12 = s.gpr .r12 + 1
  remaining : t.gpr .r15 = s.gpr .r15 - 1
  zf : t.zf = some (s.gpr .r15 - 1 == 0)
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .r14, 2048⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem frame_widen {m m' : Mem} {p : Addr} {d : Nat} {work stack headRegion : Region}
    (h : Frame [⟨p + BitVec.ofNat 64 d, 1024⟩, work, stack, headRegion] m m')
    (bound : d + 1024 ≤ 2048) : Frame [⟨p, 2048⟩, work, stack, headRegion] m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ bound⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))), fun _ h => h⟩

theorem lane_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (memory : Addr) (bytes d : Nat) (space : Space s memory bytes)
    (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d) (bound : d + 2048 ≤ bytes) :
    WP isa (lane name (HPrime.hash v)) s (LaneDone s) := by
  have ready := space.blockReady dst (by omega)
  unfold lane
  refine WP.seq ((block_ok v name s 0 ready).mono ?_)
  intro a ha
  have spaceA := space.same ha.wr (ha.regs .rbp (by decide))
    (ha.regs .rbx (by decide)) (ha.regs .rsp (by decide))
  refine WP.seq ((advance_ok a).mono ?_)
  intro b hb
  have spaceB := spaceA.same hb.wr (hb.other .rbp (by decide))
    (hb.other .rbx (by decide)) (hb.other .rsp (by decide))
  have base : b.gpr .r14 = s.gpr .r14 + 1024 := by rw [hb.destination, ha.regs .r14 (by decide)]
  have bp : b.gpr .rbp = s.gpr .rbp := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have bx : b.gpr .rbx = s.gpr .rbx := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have sp : b.gpr .rsp = s.gpr .rsp := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have laneB : b.gpr .r12 = s.gpr .r12 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have strideB : b.gpr .r13 = s.gpr .r13 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have remainingB : b.gpr .r15 = s.gpr .r15 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have dstB : b.gpr .r14 = memory + BitVec.ofNat 64 (d + 1024) := by
    rw [base, dst, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have readyB := spaceB.blockReady dstB (by omega)
  refine WP.seq ((block_ok v name b 1 readyB).mono ?_)
  intro c hc
  refine (laneEnd_ok c).mono ?_
  intro t ht
  have secondFrame := hc.frame
  rw [base, bx, sp, bp] at secondFrame
  have keptFirst : bytesAt c.mem (s.gpr .r14) 1024 = bytesAt b.mem (s.gpr .r14) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply secondFrame.bytes (R := ⟨s.gpr .r14, 1024⟩) _
      (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · rw [dst]; exact space.matrixWork.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.stackMatrix.symm.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.frameMatrix.symm.sub_left (Offset.sub_base _ (by omega)) |>.sub_right
        (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
  have h0B : bytesAt b.mem (b.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
    rw [hb.mem, bp]; exact ha.h0 ready
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),
    ht.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)), ?_⟩
  · rw [ht.mem, keptFirst, hb.mem]; exact ha.digest
  · have digest := hc.digest
    rw [base, h0B, laneB] at digest
    rw [ht.mem]; exact digest
  · rw [ht.destination, hc.regs .r14 (by decide), hc.regs .r13 (by decide), base, strideB]
    rw [BitVec.add_assoc, BitVec.add_comm (1024 : Addr), ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  · rw [ht.lane, hc.regs .r12 (by decide), laneB]
  · rw [ht.remaining, hc.regs .r15 (by decide), remainingB]
  · rw [ht.zf, hc.regs .r15 (by decide), remainingB]
  · intro r hr h14 h12 h15
    exact (ht.other r h14 h12 h15).trans ((hc.regs r hr).trans
      ((hb.other r h14).trans (ha.regs r hr)))
  · rw [ht.mem]
    rw [hb.mem] at secondFrame
    have firstFrame := frame_widen (p := s.gpr .r14) (d := 0)
      (by simpa using ha.frame)
      (by decide)
    have finalFrame := frame_widen (p := s.gpr .r14) (d := 1024)
      (by simpa only [show BitVec.ofNat 64 1024 = (1024 : Addr) from rfl] using secondFrame) (by decide)
    exact firstFrame.trans finalFrame

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitStage`. -/
section
/-! # Matrix invariant: completed lanes contain their RFC initialization blocks -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def Initialized (m : Mem) (base : Addr) (lanes q done : Nat) (h0 : List Byte) : Prop :=
  ∀ lane < lanes, ∀ column < q,
    blockAt m (base + BitVec.ofNat 64 (1024 * (lane * q + column))) =
      if lane < done ∧ column < 2 then parseBlock (Proof.Argon2.initialBytes h0 lane column)
      else zeroBlock

theorem cell_bound (lanes q lane column : Nat) (hl : lane < lanes) (hc : column < q) :
    lane * q + column < lanes * q := by
  have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ lanes by omega)
  rw [Nat.add_mul, Nat.one_mul] at mul
  omega

theorem cell_sep (q j lane column : Nat) (hq : 2 ≤ q) (hc : column < q)
    (other : lane ≠ j ∨ 2 ≤ column) :
    1024 * (lane * q + column) + 1024 ≤ 1024 * (j * q) ∨
      1024 * (j * q) + 2048 ≤ 1024 * (lane * q + column) := by
  by_cases lt : lane < j
  · have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  · by_cases gt : j < lane
    · have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lane by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    · have eq : lane = j := by omega
      subst lane
      have large : 2 ≤ column := other.elim (fun h => False.elim (h rfl)) id
      omega

theorem initialized_zero (m : Mem) (base : Addr) (lanes q : Nat)
    (bound : 1024 * (lanes * q) < 2 ^ 64) (h0 : List Byte) :
    Initialized (clearMem m base (128 * (lanes * q))) base lanes q 0 h0 := by
  intro lane hl column hc
  rw [clearMem_block _ _ _ _ bound (cell_bound _ _ _ _ hl hc)]
  simp only [Nat.not_lt_zero, false_and, ite_false]

theorem initialized_lane {s t : State} (memory : Addr) (lanes q j : Nat)
    (h0 : List Byte) (space : Space s memory (1024 * (lanes * q)))
    (hq : 2 ≤ q) (hj : j < lanes) (lanesBound : lanes < 2 ^ 64)
    (dst : s.gpr .r14 = memory + BitVec.ofNat 64 (1024 * (j * q)))
    (laneReg : s.gpr .r12 = BitVec.ofNat 64 j)
    (hash : bytesAt s.mem (s.gpr .rbp) 64 = h0)
    (initialized : Initialized s.mem memory lanes q j h0) (done : LaneDone s t) :
    Initialized t.mem memory lanes q (j + 1) h0 := by
  have laneValue : (s.gpr .r12).toNat = j := by
    rw [laneReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have currentEnd : 1024 * (j * q) + 2048 ≤ 2 ^ 64 := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    have b := space.bound
    omega
  have cellEnd (lane column : Nat) (hl : lane < lanes) (hc : column < q) :
      1024 * (lane * q + column) + 1024 ≤ 2 ^ 64 := by
    have cell := cell_bound lanes q lane column hl hc
    have b := space.bound
    omega
  intro lane hl column hc
  by_cases same : lane = j
  · subst lane
    by_cases first : column = 0
    · subst column
      rw [ite_eq_left (by omega)]
      apply Proof.Argon2.blockAt_of_initialBytes
      have eq := done.first
      rw [hash, laneValue, dst] at eq
      simpa only [Nat.add_zero] using eq
    · by_cases second : column = 1
      · subst column
        rw [ite_eq_left (by omega)]
        apply Proof.Argon2.blockAt_of_initialBytes
        have eq := done.second
        rw [hash, laneValue, dst, BitVec.add_assoc,
          show (1024 : Addr) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add] at eq
        rw [Nat.mul_add, Nat.mul_one]
        exact eq
      · have large : 2 ≤ column := by omega
        have sep := cell_sep q j j column hq hc (Or.inr large)
        have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) =
            blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) := by
          apply blockAt_frame done.frame
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [dst]; exact Offset.disjoint _ sep (cellEnd j column hj hc) currentEnd
          · exact space.matrixWork.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega))
          · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega))
          · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega)) |>.sub_right
              (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
        rw [kept, initialized j hj column hc]
        simp only [Nat.lt_irrefl, false_and, ite_false, ite_eq_right (by omega : ¬ (j < j + 1 ∧ column < 2))]
  · have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) =
        blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) := by
      apply blockAt_frame done.frame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [dst]
        exact Offset.disjoint _ (cell_sep q j lane column hq hc (Or.inl same))
          (cellEnd lane column hl hc) currentEnd
      · exact space.matrixWork.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega))
      · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega))
      · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega)) |>.sub_right
          (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
    rw [kept, initialized lane hl column hc]
    by_cases before : lane < j ∧ column < 2 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitSetup`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitClearSetup`. -/
section
/-! # Clearing the complete allocation using its public block count -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure ClearHeader (s t : State) : Prop where
  destination : t.gpr .r14 = wordAt s memoryOffset
  count : t.gpr .rax = wordAt s blocksOffset
  zero : t.gpr .rcx = 0
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clearHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8) :
    WP isa (.block clearHeader) s (ClearHeader s) := by
  apply WP.of_runBlock
  simp only [clearHeader, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.setReg32, HPrime.ea_at, memoryOffset, blocksOffset,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 232 = (232 : Addr) from rfl,
    show BitVec.ofNat 64 240 = (240 : Addr) from rfl,
    memoryRead, blocksRead, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

structure ClearSetup (s t : State) : Prop where
  destination : t.gpr .r14 = wordAt s memoryOffset
  count : t.gpr .rax = wordAt s blocksOffset * 128
  zero : t.gpr .rcx = 0
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clearSetup_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8) :
    WP isa clearSetupCode s (ClearSetup s) := by
  unfold clearSetupCode clearSetup
  rw [WP.block_append_iff]
  refine (clearHeader_ok s memoryRead blocksRead).mono ?_
  intro a ha
  refine (scale_ok a .rax 7).mono ?_
  intro b hb
  exact ⟨(hb.other _ (by decide)).trans ha.destination,
    by rw [hb.value, ha.count]; rfl,
    (hb.other _ (by decide)).trans ha.zero,
    fun r h1 h2 h3 => (hb.other r h2).trans (ha.other r h1 h2 h3),
    hb.mem.trans ha.mem, hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩

structure Cleared (s t : State) (memory : Addr) (blocks : Nat) : Prop where
  destination : t.gpr .r14 = memory + BitVec.ofNat 64 (1024 * blocks)
  other : ∀ r, r ≠ .r14 → r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = clearMem s.mem memory (128 * blocks)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem clear_ok (s : State) (memory : Addr) (blocks : Nat) (lo : 1 ≤ blocks)
    (bound : 1024 * blocks < 2 ^ 64)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 blocks)
    (cover : Covers [⟨memory, 1024 * blocks⟩] s.wr) :
    WP isa clear s fun t => Cleared s t memory blocks := by
  unfold clear
  refine WP.seq ((clearSetup_ok s memoryRead blocksRead).mono ?_)
  intro b hb
  have count : b.gpr .rax = BitVec.ofNat 64 (128 * blocks) := by
    rw [hb.count, blocksWord, show (128 : Addr) = BitVec.ofNat 64 128 from rfl,
      ← BitVec.ofNat_mul, Nat.mul_comm]
  have dst : b.gpr .r14 = memory := hb.destination.trans memoryWord
  have zero := hb.zero
  have mem := hb.mem
  have rd := hb.rd
  have wr := hb.wr
  have other := hb.other
  refine (clearLoop_ok b memory (128 * blocks) (by omega) (by omega) dst count zero ?_).mono ?_
  · intro j hj
    rw [wr]
    exact cover _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · intro t ht
    refine ⟨?_, fun r h1 h2 h3 => (ht.other r h2 h1).trans (other r h1 h2 h3), ?_,
      ht.rd.trans rd, ht.wr.trans wr⟩
    · rw [ht.destination, show 8 * (128 * blocks) = 1024 * blocks by omega]
    · rw [ht.mem, mem]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Set up the public lane loop after matrix clearing -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure LanesHeader (s t : State) : Prop where
  destination : t.gpr .r14 = wordAt s memoryOffset
  lane : t.gpr .r12 = 0
  remaining : t.gpr .r15 = wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lanesHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8) :
    WP isa (.block lanesHeader) s (LanesHeader s) := by
  apply WP.of_runBlock
  simp only [lanesHeader, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.load64, State.setReg32, HPrime.ea_at, memoryOffset, VG.Impl.Argon2.X86_64.Initial.lanesOffset,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    show BitVec.ofNat 64 232 = (232 : Addr) from rfl,
    show BitVec.ofNat 64 184 = (184 : Addr) from rfl,
    memoryRead, lanesRead, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

structure Setup (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  destination : t.gpr .r14 = memory
  lane : t.gpr .r12 = 0
  remaining : t.gpr .r15 = BitVec.ofNat 64 lanes
  stride : t.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  other : ∀ r, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → r ≠ .r13 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lanesSetup_ok (s : State) (memory : Addr) (lanes q : Nat)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (laneLength : s.gpr .r13 = BitVec.ofNat 64 q) :
    WP isa (.block lanesSetup) s fun t => Setup s t memory lanes q := by
  unfold lanesSetup
  rw [WP.block_append_iff]
  refine (lanesHeader_ok s memoryRead lanesRead).mono ?_
  intro a ha
  refine (scale_ok a .r13 10).mono ?_
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => (ht.other r h4).trans (ha.other r h1 h2 h3),
    ht.mem.trans ha.mem, ht.rd.trans ha.rd, ht.wr.trans ha.wr⟩
  · rw [ht.other .r14 (by decide), ha.destination, memoryWord]
  · rw [ht.other .r12 (by decide), ha.lane]
  · rw [ht.other .r15 (by decide), ha.remaining, lanesWord]
  · rw [ht.value, ha.other .r13 (by decide) (by decide) (by decide), laneLength,
      ← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitLoop`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitFrame`. -/
section
/-! # Effects allowed across the complete lane loop -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Spec.Blake2 (bytesAt)

def keptRegs : List Reg := [.rbp, .rbx, .rsp, .r13]

structure Keeps (s t : State) (memory : Addr) (bytes : Nat) : Prop where
  regs : ∀ r ∈ keptRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, bytes⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem Keeps.rbp {s t : State} {memory : Addr} {bytes : Nat} (h : Keeps s t memory bytes) :
    t.gpr .rbp = s.gpr .rbp := h.regs _ (by decide)
theorem Keeps.rbx {s t : State} {memory : Addr} {bytes : Nat} (h : Keeps s t memory bytes) :
    t.gpr .rbx = s.gpr .rbx := h.regs _ (by decide)
theorem Keeps.rsp {s t : State} {memory : Addr} {bytes : Nat} (h : Keeps s t memory bytes) :
    t.gpr .rsp = s.gpr .rsp := h.regs _ (by decide)

theorem Keeps.refl (s : State) (memory : Addr) (bytes : Nat) : Keeps s s memory bytes :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {s t u : State} {memory : Addr} {bytes : Nat}
    (h : Keeps s t memory bytes) (k : Keeps t u memory bytes) : Keeps s u memory bytes :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.rbx, h.rsp, h.rbp] using k.frame)⟩

theorem Space.keeps {s t : State} {memory : Addr} {bytes : Nat}
    (h : Space s memory bytes) (k : Keeps s t memory bytes) : Space t memory bytes :=
  h.same k.wr k.rbp k.rbx k.rsp

theorem Keeps.h0 {s t : State} {memory : Addr} {bytes : Nat}
    (h : Keeps s t memory bytes) (space : Space s memory bytes) :
    bytesAt t.mem (t.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
  rw [h.rbp]
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .rbp, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact space.frameMatrix.sub_left (Region.sub_prefix (by decide))
  · exact space.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact space.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem LaneDone.keeps {s t : State} (memory : Addr) (bytes d : Nat)
    (h : LaneDone s t) (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d)
    (bound : d + 2048 ≤ bytes) : Keeps s t memory bytes := by
  refine ⟨?_, h.rd, h.wr, ?_⟩
  · intro r hr
    have facts : ∀ r ∈ keptRegs, r ∈ calleeSaved ∧ r ≠ .r14 ∧ r ≠ .r12 ∧ r ≠ .r15 := by decide
    obtain ⟨cs, h14, h12, h15⟩ := facts r hr
    exact h.regs r cs h14 h12 h15
  · apply h.frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [dst]; exact Offset.sub_base _ bound⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))), fun _ h => h⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Termination and correctness of the all-lanes initialization loop -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopI (s₀ : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte) (s : State) : Prop where
  bound : j ≤ lanes
  destination : s.gpr .r14 = memory + BitVec.ofNat 64 (1024 * (j * q))
  lane : s.gpr .r12 = BitVec.ofNat 64 j
  remaining : s.gpr .r15 = BitVec.ofNat 64 (lanes - j)
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  keeps : Keeps s₀ s memory (1024 * (lanes * q))
  initialized : Initialized s.mem memory lanes q j h0
  hash : bytesAt s.mem (s.gpr .rbp) 64 = h0

theorem lane_step (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₀ s : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte)
    (space : Space s₀ memory (1024 * (lanes * q))) (hj : j < lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (h : LoopI s₀ memory lanes q j h0 s) :
    WP isa (lane name (HPrime.hash v)) s fun t =>
      LoopI s₀ memory lanes q (j + 1) h0 t ∧
      t.zf = some (decide (lanes - (j + 1) = 0)) := by
  have spaceS := space.keeps h.keeps
  have endBound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  refine (lane_ok v name s memory (1024 * (lanes * q)) (1024 * (j * q))
    spaceS h.destination endBound).mono ?_
  intro t ht
  have kt := ht.keeps memory _ _ h.destination endBound
  have nextCount : BitVec.ofNat 64 (lanes - j) - 1 = BitVec.ofNat 64 (lanes - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : LoopI s₀ memory lanes q (j + 1) h0 t := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, h.keeps.trans kt,
      initialized_lane memory lanes q j h0 spaceS hq hj lanesBound h.destination h.lane
        h.hash h.initialized ht, (kt.h0 spaceS).trans h.hash⟩
    · rw [ht.destination, h.destination, h.stride, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_mul, Nat.one_mul, Nat.mul_add]
    · rw [ht.lane, h.lane, BitVec.ofNat_add]; rfl
    · rw [ht.remaining, h.remaining, nextCount]
    · exact (kt.regs .r13 (by decide)).trans h.stride
  have zf : t.zf = some (decide (lanes - (j + 1) = 0)) := by
    rw [ht.zf, h.remaining, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lanes - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  exact ⟨next, zf⟩


theorem lanesLoop_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₀ : State) (memory : Addr) (lanes q : Nat) (h0 : List Byte)
    (space : Space s₀ memory (1024 * (lanes * q))) (lo : 1 ≤ lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (dst : s₀.gpr .r14 = memory) (laneReg : s₀.gpr .r12 = 0)
    (remaining : s₀.gpr .r15 = BitVec.ofNat 64 lanes)
    (stride : s₀.gpr .r13 = BitVec.ofNat 64 (1024 * q))
    (initialized : Initialized s₀.mem memory lanes q 0 h0)
    (hash : bytesAt s₀.mem (s₀.gpr .rbp) 64 = h0) :
    WP isa (.loop (lane name (HPrime.hash v)) .ne) s₀ (LoopI s₀ memory lanes q lanes h0) := by
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = lanes - j ∧ j < lanes ∧ LoopI s₀ memory lanes q j h0 s)
    ?_ lanes s₀ ⟨0, by omega, lo, by omega, by simpa using dst, laneReg,
      by simpa only [Nat.sub_zero] using remaining, stride, Keeps.refl _ _ _, initialized, hash⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine (lane_step v name s₀ s memory lanes q j h0 space hj lanesBound hq h).mono ?_
  intro t ⟨next, zf⟩
  by_cases done : j + 1 = lanes
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, show lanes - (j + 1) = 0 by omega, decide_true,
      Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, lanes - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, zf, show lanes - (j + 1) ≠ 0 by omega, decide_false,
      Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInit`. -/
section
/-! # Functional correctness of complete memory initialization -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)
open VG.Spec.Blake2 (bytesAt)

theorem Cleared.frame {s t : State} {memory : Addr} {blocks : Nat}
    (h : Cleared s t memory blocks) (bound : 1024 * blocks < 2 ^ 64) :
    Frame [⟨memory, 1024 * blocks⟩] s.mem t.mem := by
  rw [h.mem]
  simpa only [show 8 * (128 * blocks) = 1024 * blocks by omega] using
    clearMem_frame s.mem memory (128 * blocks) (by omega)

theorem Cleared.word {s t : State} {memory : Addr} {blocks d : Nat}
    (h : Cleared s t memory blocks) (space : Space s memory (1024 * blocks))
    (offset : d + 8 ≤ 272) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.other .rbp (by decide) (by decide) (by decide)]
  apply (h.frame space.bound).readW (r := ⟨s.gpr .rbp, 272⟩)
    (Offset.contains_base _ offset (by omega)) ?_ (by decide)
  intro r hr; simp only [List.mem_singleton] at hr; subst r
  exact space.frameMatrix

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (hq : 2 ≤ q)
    (lanesBound : lanes < 2 ^ 64) (space : Space s memory (1024 * (lanes * q)))
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q))
    (laneLength : s.gpr .r13 = BitVec.ofNat 64 q) :
    WP isa (code name (HPrime.hash v)) s fun t =>
      Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .rbp) 64) ∧
      t.gpr .rbp = s.gpr .rbp ∧ t.gpr .rbx = s.gpr .rbx ∧ t.gpr .rsp = s.gpr .rsp ∧
      t.gpr .r13 = BitVec.ofNat 64 (1024 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem := by
  unfold code lanesSetupCode
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  refine WP.seq ((clear_ok s memory (lanes * q) blocksPositive space.bound memoryRead
    blocksRead memoryWord blocksWord space.matrix).mono ?_)
  intro a ha
  have bpA := ha.other .rbp (by decide) (by decide) (by decide)
  have bxA := ha.other .rbx (by decide) (by decide) (by decide)
  have spA := ha.other .rsp (by decide) (by decide) (by decide)
  have spaceA := space.same ha.wr bpA bxA spA
  have hashA : bytesAt a.mem (a.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
    rw [bpA]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact (ha.frame space.bound).bytes (R := ⟨s.gpr .rbp, 64⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact space.frameMatrix.sub_left (Region.sub_prefix (by decide)))
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine WP.seq ((lanesSetup_ok a memory lanes q
    (by rw [ha.rd, ha.wr, bpA]; exact memoryRead)
    (by rw [ha.rd, ha.wr, bpA]; exact lanesRead)
    ((ha.word space (by decide)).trans memoryWord)
    ((ha.word space (by decide)).trans lanesWord)
    ((ha.other .r13 (by decide) (by decide) (by decide)).trans laneLength)).mono ?_)
  intro b hb
  have bpB := hb.other .rbp (by decide) (by decide) (by decide) (by decide)
  have bxB := hb.other .rbx (by decide) (by decide) (by decide) (by decide)
  have spB := hb.other .rsp (by decide) (by decide) (by decide) (by decide)
  have spaceB := spaceA.same hb.wr bpB bxB spB
  refine (lanesLoop_ok v name b memory lanes q (bytesAt s.mem (s.gpr .rbp) 64)
    spaceB lo lanesBound hq hb.destination hb.lane hb.remaining hb.stride ?_ ?_).mono ?_
  · rw [hb.mem, ha.mem]
    exact initialized_zero s.mem memory lanes q space.bound _
  · rw [hb.mem, bpB]; exact hashA
  · intro t ht
    refine ⟨ht.initialized, ht.keeps.rbp.trans (bpB.trans bpA),
      ht.keeps.rbx.trans (bxB.trans bxA), ht.keeps.rsp.trans (spB.trans spA),
      (ht.keeps.regs .r13 (by decide)).trans hb.stride, ht.keeps.rd.trans (hb.rd.trans ha.rd), ht.keeps.wr.trans (hb.wr.trans ha.wr), ?_⟩
    have fb : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
        below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem b.mem := by
      rw [hb.mem]
      exact (ha.frame space.bound).mono (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact List.mem_cons_self ..)
    apply fb.trans
    have f := ht.keeps.frame
    rw [bpB, bpA, bxB, bxA, spB, spA] at f
    exact f

/-- Every cell agrees with the reviewed initialization spec, in lane-major order. -/
theorem Initialized.spec {m : Mem} {base : Addr} {p : Spec.Argon2.Params}
    {h0 : List Byte} (hl : 0 < p.lanes) (hq : 0 < p.laneLen)
    (h : Initialized m base p.lanes p.laneLen p.lanes h0)
    (k : Nat) (hk : k < p.blocks) :
    Spec.Argon2.blockAt m (base + BitVec.ofNat 64 (1024 * k)) =
      (Spec.Argon2.initMemory p h0).memory[k]'(by
        rw [Proof.Argon2.initMemory_size]; exact hk) := by
  have blocks := Proof.Argon2.blocks_lanes p hl
  have lane : k / p.laneLen < p.lanes := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    simpa only [blocks] using hk
  have cell := h (k / p.laneLen) lane (k % p.laneLen) (Nat.mod_lt _ hq)
  rw [Nat.mul_comm (k / p.laneLen) p.laneLen, Nat.div_add_mod] at cell
  simp only [lane, true_and] at cell
  rw [Proof.Argon2.initMemory_cell p h0 k hk]
  exact cell

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitRepresent`. -/
section
/-! Memory initialization establishes the shared matrix representation invariant. -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.Spec.Argon2

theorem Initialized.represents {m : Mem} {base : Addr} {p : Params} {h0 : List Byte}
    (positive : 0 < p.lanes) (lanePositive : 0 < p.laneLen)
    (h : Initialized m base p.lanes p.laneLen p.lanes h0) :
    Proof.Argon2.Represents m base p.blocks (initMemory p h0).memory := by
  refine ⟨Proof.Argon2.initMemory_size p h0, ?_⟩
  intro k hk
  rw [Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk), Option.getD_some]
  unfold Proof.Argon2.matrixCell
  rw [Nat.mul_comm k 1024]
  exact h.spec positive lanePositive k hk

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitBlockCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitCallCT`. -/
section
/-! # Initialization's H′ calls leak only their public argument registers -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.HPrime (code)

theorem hPrime_call_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .rsi = 72 ∧ t.gpr .rsi = 72 ∧ s.gpr .rcx = 1024 ∧ t.gpr .rcx = 1024 ∧
      s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rdx = t.gpr .rdx ∧
      s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp) :
    RelCT isa P (.call name (code (HPrime.hash v))) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt, sp⟩
  change s.callEntry.gpr .rdi = t.callEntry.gpr .rdi ∧
    s.callEntry.gpr .rsi = t.callEntry.gpr .rsi ∧
    s.callEntry.gpr .rdx = t.callEntry.gpr .rdx ∧
    s.callEntry.gpr .rcx = t.callEntry.gpr .rcx ∧
    s.callEntry.gpr .r8 = t.callEntry.gpr .r8 ∧
    s.callEntry.gpr .rsp = t.callEntry.gpr .rsp
  simp only [State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, congrArg (· - 8) sp⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Public registers survive each initialization H′ call -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

def AgreeSaved (s t : State) : Prop := ∀ r ∈ calleeSaved, s.gpr r = t.gpr r

theorem blockArgs_rel (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa AgreeSaved (.block (blockArgs column)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) check

theorem block_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name (HPrime.hash v) column) AgreeSaved := by
  let P := fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t
  have args := ((blockArgs_rel column ct).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp => by
      exact ⟨blockArgs_ok s column (hp.1.prefix 64 (by decide)) (hp.1.prefix 68 (by decide)),
        blockArgs_ok t column (hp.2.1.prefix 64 (by decide)) (hp.2.1.prefix 68 (by decide))⟩)
  have call := hPrime_call_rel v name (P := fun a b =>
      True ∧ ∃ s t, P s t ∧ BlockArgs s a column ∧ BlockArgs t b column) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.ready hp.1, hb.ready hp.2.1, ha.inputLength, hb.inputLength,
      ha.outputLength, hb.outputLength, ?_, ?_, ?_, ?_⟩
    · exact ha.input.trans ((hp.2.2 .rbp (by decide)).trans hb.input.symm)
    · exact ha.output.trans ((hp.2.2 .r14 (by decide)).trans hb.output.symm)
    · exact ha.work.trans ((hp.2.2 .rbx (by decide)).trans hb.work.symm)
    · exact (ha.regs .rsp (by decide)).trans
        ((hp.2.2 .rsp (by decide)).trans (hb.regs .rsp (by decide)).symm))
  have full := (args.seq call).wpDep (fun s t hp =>
    ⟨block_ok v name s column hp.1, block_ok v name t column hp.2.1⟩)
  exact full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    intro r hr
    exact (ha.regs r hr).trans ((hp.2.2 r hr).trans (hb.regs r hr).symm))

theorem blocks_rel (v : Proof.Blake2.X86_64.Backend) (name : String) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name (HPrime.hash v) 0) AgreeSaved ∧
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name (HPrime.hash v) 1) AgreeSaved :=
  ⟨block_rel v name 0 ⟨_, by taint_decide⟩,
    block_rel v name 1 ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitLoopCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitLaneCT`. -/
section
/-! # The two leading blocks of a lane have a public execution trace -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

structure LaneReady (memory : Addr) (bytes d : Nat) (s : State) : Prop where
  space : Space s memory bytes
  destination : s.gpr .r14 = memory + BitVec.ofNat 64 d

def RelatedLane (memory : Addr) (bytes d : Nat) (s t : State) : Prop :=
  LaneReady memory bytes d s ∧ LaneReady memory bytes d t ∧ AgreeSaved s t

theorem BlockDone.laneReady {s t : State} {column : Nat} {memory : Addr} {bytes d : Nat}
    (h : BlockDone s t column) (ready : LaneReady memory bytes d s) :
    LaneReady memory bytes d t :=
  ⟨ready.space.same h.wr (h.regs .rbp (by decide)) (h.regs .rbx (by decide))
    (h.regs .rsp (by decide)), (h.regs .r14 (by decide)).trans ready.destination⟩

theorem block_lane_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true)
    (memory : Addr) (bytes d : Nat) (bound : d + 1024 ≤ bytes) :
    RelCT isa (RelatedLane memory bytes d) (block name (HPrime.hash v) column)
      (RelatedLane memory bytes d) := by
  have h := ((block_rel v name column ct).mono
    (P' := RelatedLane memory bytes d) (fun _ _ hp =>
      ⟨hp.1.space.blockReady hp.1.destination bound,
        hp.2.1.space.blockReady hp.2.1.destination bound, hp.2.2⟩)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨block_ok v name s column (hp.1.space.blockReady hp.1.destination bound),
        block_ok v name t column (hp.2.1.space.blockReady hp.2.1.destination bound)⟩)
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ha.laneReady hp.1, hb.laneReady hp.2.1, pub⟩)

theorem advance_rel : RelCT isa AgreeSaved
    (.block [.alu .add .r14 (.imm 1024)]) AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) calleeSaved
  taint_decide

theorem advance_lane_rel (memory : Addr) (bytes d : Nat) :
    RelCT isa (RelatedLane memory bytes d) (.block [.alu .add .r14 (.imm 1024)])
      (RelatedLane memory bytes (d + 1024)) := by
  have h := (advance_rel.mono (P' := RelatedLane memory bytes d)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s t _ => ⟨advance_ok s, advance_ok t⟩)
  have ready {s t : State} (h : Advanced s t) (hs : LaneReady memory bytes d s) :
      LaneReady memory bytes (d + 1024) t := by
    refine ⟨hs.space.same h.wr (h.other .rbp (by decide))
      (h.other .rbx (by decide)) (h.other .rsp (by decide)), ?_⟩
    rw [h.destination, hs.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ready ha hp.1, ready hb hp.2.1, pub⟩)

theorem laneEnd_rel : RelCT isa AgreeSaved
    (.block [.alu .add .r14 (.reg .r13), .alu .sub .r14 (.imm 1024),
      .alu .add .r12 (.imm 1), .alu .sub .r15 (.imm 1)]) AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) calleeSaved
  taint_decide

theorem lane_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (bytes d : Nat) (bound : d + 2048 ≤ bytes) :
    RelCT isa (RelatedLane memory bytes d) (lane name (HPrime.hash v)) AgreeSaved := by
  exact (block_lane_rel v name 0 ⟨_, by taint_decide⟩ memory bytes d (by omega)).seq
    ((advance_lane_rel memory bytes d).seq
    ((block_lane_rel v name 1 ⟨_, by taint_decide⟩ memory bytes (d + 1024) (by omega)).seq
      (laneEnd_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h))))

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! # Both initialization loops count only pubNext matrix dimensions -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

theorem lanesLoop_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s₁ s₂ : State) (memory : Addr) (lanes q : Nat) (h₁ h₂ : List Byte)
    (space₁ : Space s₁ memory (1024 * (lanes * q)))
    (space₂ : Space s₂ memory (1024 * (lanes * q)))
    (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q) :
    RelCT isa (fun s t => LoopI s₁ memory lanes q 0 h₁ s ∧
      LoopI s₂ memory lanes q 0 h₂ t ∧ AgreeSaved s t)
      (.loop (lane name (HPrime.hash v)) .ne) AgreeSaved := by
  let I := fun n s t => ∃ j, n = lanes - j ∧ j < lanes ∧
    LoopI s₁ memory lanes q j h₁ s ∧ LoopI s₂ memory lanes q j h₂ t ∧ AgreeSaved s t
  have steps : ∀ n, RelCT isa (I n) (lane name (HPrime.hash v)) fun a b =>
      isa.eval .ne a = isa.eval .ne b ∧
      (isa.eval .ne a = some false → AgreeSaved a b) ∧
      (isa.eval .ne a = some true → ∃ m < n, I m a b) := by
    intro n s t trace₁ trace₂ a b hp e₁ e₂
    obtain ⟨j, rfl, hj, hs, ht, pub⟩ := hp
    have bound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
      have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    have related : RelatedLane memory (1024 * (lanes * q)) (1024 * (j * q)) s t :=
      ⟨⟨space₁.keeps hs.keeps, hs.destination⟩,
        ⟨space₂.keeps ht.keeps, ht.destination⟩, pub⟩
    obtain ⟨trace, pubNext⟩ := lane_rel v name memory _ _ bound _ _ _ _ _ _ related e₁ e₂
    obtain ⟨_, a', ea, ha⟩ := lane_step v name s₁ s memory lanes q j h₁
      space₁ hj lanesBound hq hs
    obtain ⟨_, b', eb, hb⟩ := lane_step v name s₂ t memory lanes q j h₂
      space₂ hj lanesBound hq ht
    obtain ⟨-, rfl⟩ := Exec.det e₁ ea
    obtain ⟨-, rfl⟩ := Exec.det e₂ eb
    refine ⟨trace, ?_, fun _ => pubNext, ?_⟩
    · simp only [eval, ha.2, hb.2]
    · intro taken
      have remaining : lanes - (j + 1) ≠ 0 := by
        intro zero
        simp only [eval, ha.2, zero, decide_true, Option.map_some,
          Bool.not_true, Option.some.injEq, Bool.false_eq_true] at taken
      exact ⟨lanes - (j + 1), by omega, j + 1, rfl, by omega, ha.1, hb.1, pubNext⟩
  exact (RelCT.loop I steps lanes).mono (fun _ _ hp =>
    ⟨0, by omega, lo, hp.1, hp.2.1, hp.2.2⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitDone`. -/
section
/-! Merged from `Proof.Argon2.X86_64.MemoryInitClearCT`. -/
section
/-! # Matrix clearing uses only public addresses and the public allocation size -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure Ready (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8
  lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8
  blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8
  memoryWord : wordAt s memoryOffset = memory
  lanesWord : wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes
  blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q)
  laneLength : s.gpr .r13 = BitVec.ofNat 64 q

def publicBases : List Reg := [.rbp, .rbx, .rsp, .r13]

def AgreeBases (s t : State) : Prop := ∀ r ∈ publicBases, s.gpr r = t.gpr r

theorem clearSetup_rel : RelCT isa AgreeBases clearSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem clearLoop_rel : RelCT isa
    (fun s t => VG.X86_64.Taint.Agree (Taint.ofRegs (.rax :: .r14 :: publicBases)) s t)
    (.loop (.block clearWord) .ne) AgreeBases := by
  apply RelCT.taintRegs (τ := Taint.ofRegs (.rax :: .r14 :: publicBases))
    (fun _ _ h => h) publicBases
  taint_decide

theorem clear_rel (memory : Addr) (lanes q : Nat) :
    RelCT isa (fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t)
      clear AgreeBases := by
  let P := fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t
  have prep := (clearSetup_rel.mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨clearSetup_ok s h.1.memoryRead h.1.blocksRead,
        clearSetup_ok t h.2.1.memoryRead h.2.1.blocksRead⟩)
  refine prep.seq (clearLoop_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rw [ha.count, hb.count, hp.1.blocksWord, hp.2.1.blocksWord]
  · rw [ha.destination, hb.destination, hp.1.memoryWord, hp.2.1.memoryWord]
  · have excluded : ∀ r ∈ publicBases, r ≠ .r14 ∧ r ≠ .rax ∧ r ≠ .rcx := by decide
    have hn := excluded r hr
    exact (ha.other r hn.1 hn.2.1 hn.2.2).trans
      ((hp.2.2 r hr).trans (hb.other r hn.1 hn.2.1 hn.2.2).symm)

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.MemoryInitCT`. -/
section
/-! # The complete memory initialization trace depends only on public parameters -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopReady (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  initialized : Initialized s.mem memory lanes q 0 (bytesAt s.mem (s.gpr .rbp) 64)
  destination : s.gpr .r14 = memory
  lane : s.gpr .r12 = 0
  remaining : s.gpr .r15 = BitVec.ofNat 64 lanes
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * q)

theorem Cleared.ready {s t : State} {memory : Addr} {lanes q : Nat}
    (h : Cleared s t memory (lanes * q)) (hs : Ready memory lanes q s) :
    Ready memory lanes q t := by
  have bp := h.other .rbp (by decide) (by decide) (by decide)
  have bx := h.other .rbx (by decide) (by decide) (by decide)
  have sp := h.other .rsp (by decide) (by decide) (by decide)
  refine ⟨hs.space.same h.wr bp bx sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.rd, h.wr, bp]; exact hs.memoryRead
  · rw [h.rd, h.wr, bp]; exact hs.lanesRead
  · rw [h.rd, h.wr, bp]; exact hs.blocksRead
  · exact (h.word hs.space (by decide)).trans hs.memoryWord
  · exact (h.word hs.space (by decide)).trans hs.lanesWord
  · exact (h.word hs.space (by decide)).trans hs.blocksWord
  · exact (h.other .r13 (by decide) (by decide) (by decide)).trans hs.laneLength

theorem Setup.loopReady {s a b : State} {memory : Addr} {lanes q : Nat}
    (hs : Ready memory lanes q s) (ha : Cleared s a memory (lanes * q))
    (hb : Setup a b memory lanes q) : LoopReady memory lanes q b := by
  have ready := ha.ready hs
  refine ⟨ready.space.same hb.wr (hb.other .rbp (by decide) (by decide) (by decide) (by decide))
    (hb.other .rbx (by decide) (by decide) (by decide) (by decide))
    (hb.other .rsp (by decide) (by decide) (by decide) (by decide)), ?_,
    hb.destination, hb.lane, hb.remaining, hb.stride⟩
  rw [hb.mem, ha.mem]
  exact initialized_zero s.mem memory lanes q hs.space.bound _

theorem lanesSetup_rel : RelCT isa AgreeBases lanesSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem Setup.agree {s t a b : State} {memory : Addr} {lanes q : Nat}
    (ha : Setup s a memory lanes q) (hb : Setup t b memory lanes q)
    (hp : AgreeBases s t) : AgreeSaved a b := by
  intro r hr
  by_cases h14 : r = .r14
  · subst r; exact ha.destination.trans hb.destination.symm
  by_cases h12 : r = .r12
  · subst r; exact ha.lane.trans hb.lane.symm
  by_cases h15 : r = .r15
  · subst r; exact ha.remaining.trans hb.remaining.symm
  by_cases h13 : r = .r13
  · subst r; exact ha.stride.trans hb.stride.symm
  have included : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → r ≠ .r13 →
      r ∈ publicBases := by decide
  exact (ha.other r h14 h12 h15 h13).trans
    ((hp r (included r hr h14 h12 h15 h13)).trans (hb.other r h14 h12 h15 h13).symm)

theorem lanesLoop_ready_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    RelCT isa (fun s t => LoopReady memory lanes q s ∧ LoopReady memory lanes q t ∧
      AgreeSaved s t) (.loop (lane name (HPrime.hash v)) .ne) AgreeSaved := by
  intro s t ts tt a b hp es et
  have initial {s : State} (h : LoopReady memory lanes q s) :
      LoopI s memory lanes q 0 (bytesAt s.mem (s.gpr .rbp) 64) s :=
    ⟨by omega, by simpa using h.destination, h.lane,
      by simpa only [Nat.sub_zero] using h.remaining, h.stride, Keeps.refl _ _ _,
      h.initialized, rfl⟩
  exact lanesLoop_rel v name s t memory lanes q _ _ hp.1.space hp.2.1.space lo
    lanesBound hq _ _ _ _ _ _ ⟨initial hp.1, initial hp.2.1, hp.2.2⟩ es et

theorem code_ct (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    ConstantTime isa (Ready memory lanes q) AgreeBases (code name (HPrime.hash v)) := by
  let P := fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  have cleared := (clear_rel memory lanes q).wpDep (fun s t hp =>
    ⟨clear_ok s memory (lanes * q) blocksPositive hp.1.space.bound hp.1.memoryRead
        hp.1.blocksRead hp.1.memoryWord hp.1.blocksWord hp.1.space.matrix,
      clear_ok t memory (lanes * q) blocksPositive hp.2.1.space.bound hp.2.1.memoryRead
        hp.2.1.blocksRead hp.2.1.memoryWord hp.2.1.blocksWord hp.2.1.space.matrix⟩)
  let R := fun a b => AgreeBases a b ∧ ∃ s t, P s t ∧
    Cleared s a memory (lanes * q) ∧ Cleared t b memory (lanes * q)
  have setup := (lanesSetup_rel.mono (P' := R) (fun _ _ h => h.1)
    (fun _ _ h => h)).wpDep (F := fun a b => Setup a b memory lanes q) (by
    intro a b hp
    obtain ⟨_, s, t, hst, ha, hb⟩ := hp
    have ra := ha.ready hst.1
    have rb := hb.ready hst.2.1
    exact ⟨lanesSetup_ok a memory lanes q ra.memoryRead ra.lanesRead ra.memoryWord
        ra.lanesWord ra.laneLength,
      lanesSetup_ok b memory lanes q rb.memoryRead rb.lanesRead rb.memoryWord
        rb.lanesWord rb.laneLength⟩)
  have prepared : RelCT isa R lanesSetupCode (fun a b =>
      LoopReady memory lanes q a ∧ LoopReady memory lanes q b ∧ AgreeSaved a b) := setup.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, c, d, hp, ha, hb⟩ := h
    obtain ⟨pub, s, t, hst, hc, hd⟩ := hp
    exact ⟨ha.loopReady hst.1 hc, hb.loopReady hst.2.1 hd, ha.agree hb pub⟩)
  exact (cleared.seq (prepared.seq (lanesLoop_ready_rel v name memory lanes q lo
    lanesBound hq))).constantTime

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Initialization retains its byte stride and every public frame word outside its lane suffix. -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  initialized : Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .rbp) 64)
  bp : t.gpr .rbp = s.gpr .rbp
  bx : t.gpr .rbx = s.gpr .rbx
  sp : t.gpr .rsp = s.gpr .rsp
  stride : t.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem complete_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (memory : Addr) (lanes q : Nat) (ready : Ready memory lanes q s)
    (positive : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (minimum : 2 ≤ q) :
    WP isa (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)) s (Done s · memory lanes q) :=
  (code_ok v name s memory lanes q positive minimum lanesBound ready.space ready.memoryRead ready.lanesRead
    ready.blocksRead ready.memoryWord ready.lanesWord ready.blocksWord ready.laneLength).mono
      (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)

theorem Done.frame_word {s t : State} {memory : Addr} {lanes q : Nat}
    (space : Space s memory (1024 * (lanes * q))) (done : Done s t memory lanes q)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 64 ∨ 72 ≤ d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64 := by
  rw [done.bp]
  have sub : Region.Sub ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact space.frameMatrix.sub_left sub
    · exact space.frameWork.sub_left sub
    · exact space.stackFrame.symm.sub_left sub
    · exact Offset.disjoint (s.gpr .rbp) separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.MemoryInit
end

/-! Merged from `Proof.Argon2.X86_64.InitFillReady`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSetupReset`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSetupDimensions`. -/
section
/-! Initialization's byte stride gives exact block and segment counts without division instructions. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

theorem dimensions_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.FillSetup.dimensions) s fun t =>
    t.gpr .r12 = s.gpr .r13 >>> 10 ∧ t.gpr .r13 = s.gpr .r13 >>> 12 ∧ Divide.Keeps [.r12, .r13] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FillSetup.dimensions, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    show 1 ≤ (10 : Nat) ∧ (10 : Nat) ≤ 63 from by decide,
    show 1 ≤ (12 : Nat) ∧ (12 : Nat) ≤ 63 from by decide,
    and_self, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem stride_shift (q shift : Nat) (bound : 1024 * q < 2 ^ 64) :
    BitVec.ofNat 64 (1024 * q) >>> shift = BitVec.ofNat 64 ((1024 * q) / 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) bound)]

theorem dimensions_nat_ok (s : State) (p : Params) (bound : 1024 * p.laneLen < 2 ^ 64)
    (stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * p.laneLen)) :
    WP isa (.block Impl.Argon2.X86_64.FillSetup.dimensions) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 p.laneLen ∧ t.gpr .r13 = BitVec.ofNat 64 p.segmentLen ∧
      Divide.Keeps [.r12, .r13] s t := by
  refine (dimensions_ok s).mono ?_
  rintro t ⟨lane, segment, keeps⟩
  refine ⟨?_, ?_, keeps⟩
  · rw [lane, stride, stride_shift _ 10 bound]
    simp only [show 2 ^ 10 = 1024 from rfl, Nat.mul_div_cancel_left _ (by decide : 0 < 1024)]
  · rw [segment, stride, stride_shift _ 12 bound]
    have div : 1024 * p.laneLen / 4096 = p.laneLen / 4 := by
      rw [show (4096 : Nat) = 1024 * 4 from rfl, Nat.mul_div_mul_left _ _ (by decide : 0 < 1024)]
    rw [show 2 ^ 12 = 4096 from rfl, div]
    rfl

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Reset public loop coordinates and only the pass word in the enclosing frame. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Reset (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .rbp) 0) (0 : Addr)
  lane : t.gpr .rbx = 0
  slice : t.gpr .r14 = 0
  regs : ∀ r, r ∉ [Reg.rax, .rbx, .r14] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem reset_ok (s : State) (write : InRegions s.wr (off (s.gpr .rbp) 0) 8) :
    WP isa (.block Impl.Argon2.X86_64.FillSetup.reset) s (Reset s) := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FillSetup.reset, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    write, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

theorem Reset.pass {s t : State} (h : Reset s t) : t.mem.readW (off (t.gpr .rbp) 0) 64 = 0 := by
  rw [h.mem, h.regs .rbp (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem Reset.frame {s t : State} (h : Reset s t) : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (r := ⟨s.gpr .rbp, 8⟩) (by simp) _
    (by simpa only [off, BitVec.add_zero] using Region.contains_self (s.gpr .rbp) 8)

theorem Reset.read {s t : State} (h : Reset s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.mem, h.regs .rbp (by decide)]
  exact Mem.readW_writeW_sep (w := 64) (w' := 64)
    (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Merged from `Proof.Argon2.X86_64.FillSetupFinish`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillSetupEnvironment`. -/
section
/-! Initialization hands filling the reviewed dimensions and stable public frame words. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Environment (p : Params) (s : State) : Prop where
  parameters : FillContext.Parameters p 0 0 0
  passesBound : p.passes < 2 ^ 32
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  counterWrite : InRegions s.wr (off (s.gpr .rbp) 8) 8
  passWrite : InRegions s.wr (off (s.gpr .rbp) 0) 8
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Environment.of_state {p : Params} {s t : State} (h : Environment p s)
    (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.passesBound, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.counterWrite
  · rw [wr, bp]; exact h.passWrite
  · rw [base, work]; exact h.matrixWork
  all_goals rw [mem, bp]
  · exact h.blocksWord
  · exact h.passesWord
  · exact h.variantWord
  · exact h.lanesWord

theorem Reset.header {p : Params} {s t : State} (h : Environment p s) (reset : Reset s t)
    (laneLength : t.gpr .r12 = BitVec.ofNat 64 p.laneLen)
    (segmentLength : t.gpr .r13 = BitVec.ofNat 64 p.segmentLen) : FillHeader.Ready p 0 0 0 t := by
  have bp := reset.regs .rbp (by decide)
  have sp := reset.regs .rsp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := reset.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := reset.read 248 (by decide) (by decide)
  refine ⟨h.layout.of_preserved bp sp base work reset.rd reset.wr, ?_, ?_, ?_, ?_, ?_, laneLength,
    segmentLength, (reset.read 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [reset.rd, reset.wr, bp]; exact h.addressLayout.frameRead
    · rw [reset.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [reset.rd, reset.wr, bp]; exact h.reads
  · rw [reset.wr, bp]; exact h.counterWrite
  · refine ⟨(s.mem.readW (off (s.gpr .rbp) 8) 64).toNat, reset.pass, reset.lane, reset.slice,
      (reset.read 240 (by decide) (by decide)).trans h.blocksWord,
      (reset.read 72 (by decide) (by decide)).trans h.passesWord,
      (reset.read 112 (by decide) (by decide)).trans h.variantWord, ?_⟩
    rw [reset.read 8 (by decide) (by decide)]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Merged from `Proof.Argon2.X86_64.FillSetup`. -/
section
/-! Establish the complete pass-loop invariant from memory initialization's byte stride. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  environment : Environment p s
  bound : 1024 * p.laneLen < 2 ^ 64
  stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * p.laneLen)

structure Prepared (s t : State) (p : Params) : Prop where
  ready : FillIterations.Ready p 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  words : ∀ d, 8 ≤ d → d + 8 ≤ 272 →
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.X86_64.FillSetup.code s (Prepared s · p) := by
  unfold Impl.Argon2.X86_64.FillSetup.code
  refine WP.seq ((dimensions_nat_ok s p h.bound h.stride).mono ?_)
  rintro a ⟨laneLength, segmentLength, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
  have environment := h.environment.of_state bp sp keeps.mem keeps.rd keeps.wr
  refine (reset_ok a environment.passWrite).mono ?_
  intro t reset
  have header := reset.header environment ((reset.regs .r12 (by decide)).trans laneLength)
    ((reset.regs .r13 (by decide)).trans segmentLength)
  have words (d : Nat) (lower : 8 ≤ d) (upper : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [reset.read d lower upper, keeps.mem, bp]
  refine ⟨⟨⟨environment.parameters, 0, 0, header⟩, environment.passesBound, ?_⟩,
    words 232 (by decide) (by decide), words 248 (by decide) (by decide), ?_,
    reset.rd.trans keeps.rd, reset.wr.trans keeps.wr, ?_, reset.mxcsr.trans keeps.mxcsr, words⟩
  · rw [reset.wr, reset.regs .rbp (by decide)]; exact environment.passWrite
  · intro r hr bx q g sl
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reset.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ne, bx, sl⟩)).trans
      (keeps.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨q, g⟩))
  · have frame := reset.frame
    rw [bp, keeps.mem] at frame; exact frame

theorem Prepared.represents {s t : State} {p : Params} (ready : Ready p s) (done : Prepared s t p)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [done.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame done.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.environment.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Region.sub_prefix (by decide))

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.FillSetup.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Filling setup retains the final-call layout and establishes the reduction dimensions. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

theorem Prepared.finish_ready {s t : State} {p : Params} (ready : Ready p s) (done : Prepared s t p)
    (outputReady : FinalOutput.Ready p s) (positive : 0 < p.passes) : FillFinish.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have base : ReductionState.matrix t = ReductionState.matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.words 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.words 248 (by decide) (by decide)
  obtain ⟨lane, slice, header⟩ := done.ready.filling.header
  have params := ready.environment.parameters
  refine ⟨done.ready, ⟨?_, ?_⟩, positive⟩
  · refine ⟨⟨params.lanesPositive, params.segment_bound.1, ?_, header.layout.frameRead 232 (by simp),
      header.layout.matrixWrite, header.layout.matrixFrame, header.laneLength⟩,
      params.lanesBound, header.layout.frameRead 184 (by simp), header.lanesWord⟩
    have blocks := Proof.Argon2.blocks_le_memory p
    have memory := params.memoryBound
    omega
  · refine ⟨outputReady.positive, outputReady.bound, ?_,
      (done.words 264 (by decide) (by decide)).trans outputReady.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [done.rd, done.wr, bp]; exact outputReady.reads
    · rw [base, done.rd, done.wr]; exact outputReady.input
    · rw [output, done.wr]; exact outputReady.outputWrite
    · rw [work, done.wr]; exact outputReady.workWrite
    · rw [base, work]; exact outputReady.inputWork
    · rw [output, work]; exact outputReady.outputWork
    · rw [sp, base]; exact outputReady.stackInput
    · rw [sp, output]; exact outputReady.stackOutput
    · rw [sp, work]; exact outputReady.stackWork

end VG.Proof.Argon2.X86_64.FillSetup
end

/-! Retain the filling environment and final-call layout across memory initialization. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  initializing : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen s
  environment : FillSetup.Environment p s
  output : FinalOutput.Ready p s
  positive : 0 < p.passes
  scratch : s.gpr .rbx = FinalOutput.work s

theorem initialized_environment {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.bp done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.bp]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.bp, work]; exact e.addressLayout.frameWork
    · rw [done.bp, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.bp]; exact e.reads
  · rw [done.wr, done.bp]; exact e.counterWrite
  · rw [done.wr, done.bp]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word h.initializing.space 240 (by decide) (Or.inr (by decide))).trans e.blocksWord
  · exact (done.frame_word h.initializing.space 72 (by decide) (Or.inr (by decide))).trans e.passesWord
  · exact (done.frame_word h.initializing.space 112 (by decide) (Or.inr (by decide))).trans e.variantWord
  · exact (done.frame_word h.initializing.space 184 (by decide) (Or.inr (by decide))).trans e.lanesWord

theorem initialized_output {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  refine ⟨h.output.positive, h.output.bound, ?_,
    (done.frame_word h.initializing.space 264 (by decide) (Or.inr (by decide))).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.bp]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem initialized_setup {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Ready p t := by
  have params := h.environment.parameters
  have product : p.laneLen ≤ p.lanes * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ p.lanes from params.lanesPositive)
  refine ⟨initialized_environment h done, ?_, done.stride⟩
  have bound := h.initializing.space.bound
  have bytes := Nat.mul_le_mul_left 1024 product
  omega

theorem initialized_represents {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
      (initMemory p (Spec.Blake2.bytesAt s.mem (s.gpr .rbp) 64)).memory := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  rw [base]
  have segments := Proof.Argon2.laneLen_segments p h.environment.parameters.lanesPositive
  have minimum := h.environment.parameters.segment_bound.1
  exact done.initialized.represents h.environment.parameters.lanesPositive (by omega)

end VG.Proof.Argon2.X86_64.InitFill
end

/-! Merged from `Proof.Argon2.X86_64.InitFillFrames`. -/
section
/-! Each stage writes only the matrix, hash scratch, output, call stack and local hash prefix. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨FinalOutput.work s, 16384⟩,
    ⟨FinalOutput.output s, p.tagLen⟩, below (s.gpr .rsp) 24, ⟨s.gpr .rbp, 72⟩]

theorem initialization_frame {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have blocks := Proof.Argon2.blocks_lanes p h.environment.parameters.lanesPositive
    exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [writes], by rw [blocks, Nat.mul_comm 1024]; intro _ h; exact h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [writes], by rw [h.scratch]; intro _ h; exact h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem setup_frame {s t : State} {p : Params} (h : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .rbp, 72⟩, by simp [writes], Region.sub_prefix (by decide)⟩

theorem filling_frame {s t : State} {p : Params} (positive : 0 < p.blocks) (h : Frame (FillFinish.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillFinish.writes, FillIterations.writes, Finish.writes,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.gpr .rsp) 24, by simp [writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [writes], Region.sub_prefix (by omega)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.InitFill
end

/-! Exact initialization, every filling pass, final reduction and H′ after the reviewed H₀. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def result (p : Params) (h0 : List Byte) : List Byte :=
  Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes (initMemory p h0)).memory

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = result p (bytesAt s.mem (s.gpr .rbp) 64)
  bp : t.gpr .rbp = s.gpr .rbp
  sp : t.gpr .rsp = s.gpr .rsp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem

theorem writes_eq (s t : State) (p : Params) (bp : t.gpr .rbp = s.gpr .rbp) (sp : t.gpr .rsp = s.gpr .rsp)
    (base : FillKernel.matrix t = FillKernel.matrix s) (work : FinalOutput.work t = FinalOutput.work s)
    (output : FinalOutput.output t = FinalOutput.output s) : writes t p = writes s p := by
  unfold writes
  rw [bp, sp, base, work, output]

theorem code_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (p : Params) (h : Ready p s) :
    WP isa (Impl.Argon2.X86_64.InitFill.code name (HPrime.hash v)) s (Done s · p) := by
  have params := h.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have blocks := Proof.Argon2.lastIndex_bounds p params.lanesPositive params.segment_bound.1 0 params.lanesPositive
  unfold Impl.Argon2.X86_64.InitFill.code
  refine WP.seq ((MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen h.initializing
    params.lanesPositive (Nat.lt_trans params.lanesBound (by decide)) q).mono ?_)
  intro a initialized
  have setupReady := initialized_setup h initialized
  have initializedBase : FillKernel.matrix a = FillKernel.matrix s :=
    initialized.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have initializedWork : FinalOutput.work a = FinalOutput.work s :=
    initialized.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have initializedOutput : FinalOutput.output a = FinalOutput.output s :=
    initialized.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have rep : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks
      (initMemory p (bytesAt s.mem (s.gpr .rbp) 64)).memory := by
    rw [initializedBase]
    exact initialized.initialized.represents params.lanesPositive (by omega)
  refine WP.seq ((FillSetup.code_ok a p setupReady).mono ?_)
  intro b prepared
  refine (FillFinish.code_ok v name b p (prepared.finish_ready setupReady (initialized_output h initialized) h.positive)
    (initMemory p (bytesAt s.mem (s.gpr .rbp) 64)) (prepared.represents setupReady _ rep)).mono ?_
  intro t filled
  have bp := prepared.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have sp := prepared.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide) (by decide)
  have work : FinalOutput.work b = FinalOutput.work a := prepared.words 248 (by decide) (by decide)
  have output : FinalOutput.output b = FinalOutput.output a := prepared.words 256 (by decide) (by decide)
  refine ⟨?_, (filled.regs .rbp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans (bp.trans initialized.bp),
    (filled.regs .rsp (by simp [calleeSaved]) (by decide) (by decide) (by decide)).trans (sp.trans initialized.sp),
    filled.rd.trans (prepared.rd.trans initialized.rd), filled.wr.trans (prepared.wr.trans initialized.wr), ?_⟩
  · have digest := filled.digest
    rw [output, initializedOutput] at digest
    exact digest
  · have initialFrame := initialization_frame h initialized
    have setupFrame := setup_frame (p := p) prepared.frame
    rw [writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at setupFrame
    have fillFrame := filling_frame (by omega : 0 < p.blocks) filled.frame
    rw [writes_eq a b p bp sp prepared.matrix work output,
      writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at fillFrame
    exact (initialFrame.trans setupFrame).trans fillFrame

theorem result_derive (p : Params) (password salt secret ad : List Byte) :
    result p (initialHash p password salt secret ad) = derive p password salt secret ad := by
  unfold result derive
  rw [Proof.Argon2.iterations_fill]

end VG.Proof.Argon2.X86_64.InitFill
