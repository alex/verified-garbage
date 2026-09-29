import VerifiedGarbage.Proof.Sha1.Arm.Rounds
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.Arm.Target

/-!
# SHA-1 compression function on ARMv7: the whole function

Untrusted: everything here is checked by Lean.
-/

/-!
## SHA-1: the 32-bit ARM contract

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the 32-bit ARM
implementations of the compression function and of the streaming functions
(`init`, `update`, `finalize`; see `VG.Spec.Sha1.Repr`), in terms of
`Spec/Sha1.lean`. The streaming contracts are those of x86-64 and AArch64
(`Proof/Sha1/X86_64/Compress.lean`, `Proof/Sha1/AArch64/Compress.lean`), with
the arguments where AAPCS passes them.
-/

namespace VG.Proof.Sha1

open Spec.Sha1

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_compress(state: *mut [u32; 5], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 14])`:
updates the hash value at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(20 bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, and none of them may wrap around the end of
the (32-bit) address space. The pointers and `n` are public; the hash value
and the blocks are secret. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 20⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 112⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + 20 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 112 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      compressBlocks (stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

open VG.Arm in
/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

open VG.Arm in
/-- 32-bit ARM contract for `vg_sha1_init(state: *mut [u8; 84])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (84 bytes), which may not wrap around the end of
the (32-bit) address space. The pointer is public. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    s.rd = [] ∧ s.wr = [state] ∧ (s.gpr .r0).toNat + 84 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_update(state: *mut [u8; 84], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `data`, `len` and
`scratch` are the stack arguments 0, 1 and 2. The code may read those
arguments (12 bytes at `sp`) and `data` (`len` bytes), and read and write
`state` (84 bytes) and `scratch` (160 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, the data or
the arguments; the data may not overlap them either; and nothing may wrap
around the end of the (32-bit) address space. `sp`, the pointers, `count`
and `len` are public; the state and the data are secret. -/
def updateArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 84 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    Repr s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

open VG.Arm in
/-- 32-bit ARM contract for
`vg_sha1_finalize(state: *mut [u8; 84], count: u64, out: *mut [u8; 20], scratch: *mut [u64; 20])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the SHA-1 digest of `m` to `out`.

Under AAPCS, `state` is in `r0`, `count` in `r2:r3`, and `out` and `scratch`
are the stack arguments 0 and 1. The code may read those arguments (8 bytes
at `sp`), and read and write `state` (84 bytes, whose contents on exit are
unspecified), `out` (20 bytes) and `scratch` (160 bytes, whose contents on
exit are unspecified). These may not overlap each other or the arguments,
and nothing may wrap around the end of the (32-bit) address space. `sp`, the
pointers and `count` are public; the state is secret. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 84⟩
    let out : Region := ⟨State.addr (stackArg s 0), 20⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 160⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 84 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 20 ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 160 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ m, Repr s.mem (State.addr (s.gpr .r0)) m → countArm s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) 20 = Spec.Sha1.hash m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha1


namespace VG.Proof.Sha1.Arm

open VG VG.Arm VG.Impl.Sha1.Arm
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev bp : BitVec 32 := s₀.gpr .r1
abbrev nb : Nat := (s₀.gpr .r2).toNat
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev stR : Region := ⟨State.addr (st s₀), 20⟩
abbrev blR : Region := ⟨State.addr (bp s₀), 64 * nb s₀⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (State.addr (st s₀))

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (State.addr (bp s₀) + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := State.addr (st s₀ + BitVec.ofNat 32 (4 * k))

/-- The address of a saved register. -/
abbrev saveAddr (d : Nat) : Addr := State.addr (scr s₀ + BitVec.ofNat 32 d)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 20 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 5) :
    stAddr s₀ k = State.addr (st s₀) + BitVec.ofNat 64 (4 * k) :=
  addr_add (by have := h.st_fits; omega)

theorem saveAddr_eq {d : Nat} (hd : d < 112) :
    saveAddr s₀ d = State.addr (scr s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := h.scr_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t)) =
      State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_add (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega),
    addr_add (by omega)]

theorem in_state {k : Nat} (hk : k < 5) : InRegions (s₀.rd ++ s₀.wr) (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem out_state {k : Nat} (hk : k < 5) : InRegions s₀.wr (stAddr s₀ k) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_sub (by omega) (by omega) (h.stAddr_eq hk)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega) (by simp only [slot]; omega)
    (slotAddr_eq h.scr_fits j)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub (by simp only [slot]; omega) (by simp only [slot]; omega)
    (slotAddr_eq h.scr_fits j)⟩

theorem in_save {d : Nat} (hd : d + 4 ≤ 112) : InRegions (s₀.rd ++ s₀.wr) (saveAddr s₀ d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.saveAddr_eq (by omega))⟩

theorem out_save {d : Nat} (hd : d + 4 ≤ 112) : InRegions s₀.wr (saveAddr s₀ d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.saveAddr_eq (by omega))⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    State.addr (bp s₀) + BitVec.ofNat 64 (64 * i + 4 * t) by bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 5) (hk : k < 5) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := by
  intro x hx hy
  bv_omega

/-- Reading word `j` of the hash value after writing word `k`. -/
theorem readW_writeW_word {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {j k : Nat} (hj : j < 5)
    (hk : k < 5) (h : j ≠ k) :
    (m.writeW (stAddr s₀ k) v).readW (stAddr s₀ j) 32 = m.readW (stAddr s₀ j) 32 := by
  rw [hp.stAddr_eq hj, hp.stAddr_eq hk]
  exact Mem.readW_writeW_sep (word_sep _ hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 5) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m (State.addr (st s₀)) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 5) :
    (stateAt m (State.addr (st s₀)))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (saveAddr s₀ 64) 32 = s₀.gpr .r4 ∧ m.readW (saveAddr s₀ 68) 32 = s₀.gpr .r5 ∧
  m.readW (saveAddr s₀ 72) 32 = s₀.gpr .r6 ∧ m.readW (saveAddr s₀ 76) 32 = s₀.gpr .r7 ∧
  m.readW (saveAddr s₀ 80) 32 = s₀.gpr .r8 ∧ m.readW (saveAddr s₀ 84) 32 = s₀.gpr .r9 ∧
  m.readW (saveAddr s₀ 88) 32 = s₀.gpr .r10 ∧ m.readW (saveAddr s₀ 92) 32 = s₀.gpr .r11 ∧
  m.readW (saveAddr s₀ 96) 32 = s₀.gpr .lr

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = st s₀
  r3 : s.gpr .r3 = scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (State.addr (st s₀)) =
    compressBlocks (H₀ s₀) s₀.mem (State.addr (bp s₀)) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r1 : s.gpr .r1 = blkAddr s₀ i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .ldr .r4 .r0 (4 * 0), .ldr .r5 .r0 (4 * 1), .ldr .r6 .r0 (4 * 2), .ldr .r7 .r0 (4 * 3),
    .ldr .r8 .r0 (4 * 4)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .r12 .r0 (4 * 0), .dp .add .r4 .r4 (.reg .r12), .str .r4 .r0 (4 * 0),
    .ldr .r12 .r0 (4 * 1), .dp .add .r5 .r5 (.reg .r12), .str .r5 .r0 (4 * 1),
    .ldr .r12 .r0 (4 * 2), .dp .add .r6 .r6 (.reg .r12), .str .r6 .r0 (4 * 2),
    .ldr .r12 .r0 (4 * 3), .dp .add .r7 .r7 (.reg .r12), .str .r7 .r0 (4 * 3),
    .ldr .r12 .r0 (4 * 4), .dp .add .r8 .r8 (.reg .r12), .str .r8 .r0 (4 * 4),
    .dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .r4 = v[0] ∧ s.gpr .r5 = v[1] ∧ s.gpr .r6 = v[2] ∧ s.gpr .r7 = v[3] ∧
    s.gpr .r8 = v[4] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr0 : s.gpr .r0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (State.addr (st s₀))) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32,
    hr0, h0, h1, h2, h3, h4, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 5 by decide), stateAt_get hp _ (show 1 < 5 by decide),
    stateAt_get hp _ (show 2 < 5 by decide), stateAt_get hp _ (show 3 < 5 by decide),
    stateAt_get hp _ (show 4 < 5 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Five words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  (((((m.writeW (stAddr s₀ 0) v[0]).writeW (stAddr s₀ 1) v[1]).writeW (stAddr s₀ 2) v[2]).writeW
    (stAddr s₀ 3) v[3]).writeW (stAddr s₀ 4) v[4])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) (State.addr (st s₀)) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ k, k < 5 → (stR s₀).Contains (stAddr s₀ k) (32 / 8) :=
    fun k hk => contains_sub (by omega) (by omega) (hp.stAddr_eq hk)
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr0 : s.gpr .r0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r1 = s.gpr .r1 + 64 ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 5 →
      InRegions (s.rd ++ s.wr) (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 5 → InRegions s.wr (State.addr (st s₀ + BitVec.ofNat 32 (4 * k))) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    State.load32, State.store32, subFlags, hr0,
    i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    readW_writeW_word hp,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  and_intros
  · simp only [writeState, Vector.getElem_zipWith]
  all_goals trivial

theorem save_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (saveAddr s₀ d) 4 (saveAddr s₀ e) 4 := by
  intro x hx hy
  rw [hp.saveAddr_eq (by omega)] at hx
  rw [hp.saveAddr_eq (by omega)] at hy
  generalize State.addr (scr s₀) = a at *
  bv_omega

theorem readW_writeW_save {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (saveAddr s₀ e) v).readW (saveAddr s₀ d) 32 = m.readW (saveAddr s₀ d) 32 :=
  Mem.readW_writeW_sep (save_sep hp hd he h) (by decide)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [winRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 64 ≤ d → d + 4 ≤ 112 →
      m'.readW (saveAddr s₀ d) 32 = m.readW (saveAddr s₀ d) 32 := by
    intro d hd hd'
    have hc : (⟨saveAddr s₀ d, 4⟩ : Region).Contains (saveAddr s₀ d) (32 / 8) :=
      Region.contains_self _ _
    rcases hf with hf | hf
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [hp.saveAddr_eq (by omega)] at h₁
      generalize State.addr (scr s₀) = b at *
      bv_omega
    · refine hf.readW hc ?_ (by decide)
      simp only [List.mem_singleton, forall_eq]
      refine Region.Disjoint.sub_left hp.st_scr.symm fun a ha => ?_
      simp only [Region.Contains] at ha ⊢
      rw [hp.saveAddr_eq (by omega)] at ha
      generalize State.addr (scr s₀) = b at *
      bv_omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨(key 64 (by omega) (by omega)).trans h1, (key 68 (by omega) (by omega)).trans h2,
    (key 72 (by omega) (by omega)).trans h3, (key 76 (by omega) (by omega)).trans h4,
    (key 80 (by omega) (by omega)).trans h5, (key 84 (by omega) (by omega)).trans h6,
    (key 88 (by omega) (by omega)).trans h7, (key 92 (by omega) (by omega)).trans h8,
    (key 96 (by omega) (by omega)).trans h9⟩

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    rev (s₀.mem.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, rev_readW]
  simp only [blk, blockAt, parseBlock]
  generalize State.addr (bp s₀) + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) by bv_omega,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) by bv_omega,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) by bv_omega]

theorem win_sub (p : BitVec 32) : Region.Sub (winRegion p) ⟨State.addr p, 112⟩ :=
  Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev (m.readW (State.addr (blkAddr s₀ i + BitVec.ofNat 32 (4 * t))) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  have hr1₁ : s₁.gpr .r1 = blkAddr s₀ i := (hpub₁ .r1 (by decide)).trans hL.r1
  have hr3₁ : s₁.gpr .r3 = scr s₀ := (hpub₁ .r3 (by decide)).trans hL.r3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hp.scr_fits hr1₁ hr3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hr0₂ : s₂.gpr .r0 = st s₀ := by rw [pub₂ .r0 (by decide), hL.r0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (State.addr (st s₀))) hR.vars hr0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_sub (by omega) (by omega) (hp.stAddr_eq hk)) hst (by decide), hm₁,
      stateAt_get hp _ hk]
  obtain ⟨hm₃, hr1₃, hr2₃, hz₃, hr0₃, hr3₃, hrd₃, hwr₃⟩ := h₃
  have hnb : nb s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt
  have hr2 : s₂.gpr .r2 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [pub₂ .r2 (by decide), hL.r2]
    bv_omega
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState hp (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr0₃, hr0₂], by rw [hr3₃, pub₂ .r3 (by decide), hL.r3],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_, ?_⟩
    · rw [hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
      rfl
    · rw [hm₃]
      refine saved_frame hp ?_ (.inr (frame_writeState hp (Frame.refl _ _) _))
      refine saved_frame hp ?_ (.inl hR.frame)
      rw [hm₁]; exact hL.saved
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₃, hr2]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with r1 := ?_, r2 := ?_ }⟩
    · rw [hr1₃, pub₂ .r1 (by decide), hL.r1]
      simp only [blkAddr]
      bv_omega
    · rw [hr2₃, hr2]

/-! ## Prologue and epilogue -/

theorem save_eq : save ++ ([.cmp .r2 (.imm 0)] : List Instr) = [
    .str .r4 .r3 64, .str .r5 .r3 68, .str .r6 .r3 72, .str .r7 .r3 76, .str .r8 .r3 80,
    .str .r9 .r3 84, .str .r10 .r3 88, .str .r11 .r3 92, .str .lr .r3 96,
    .cmp .r2 (.imm 0)] := rfl

theorem restore_eq : restore = [
    .ldr .r4 .r3 64, .ldr .r5 .r3 68, .ldr .r6 .r3 72, .ldr .r7 .r3 76, .ldr .r8 .r3 80,
    .ldr .r9 .r3 84, .ldr .r10 .r3 88, .ldr .r11 .r3 92, .ldr .lr .r3 96] := rfl

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  ((((((((s₀.mem.writeW (saveAddr s₀ 64) (s₀.gpr .r4)).writeW (saveAddr s₀ 68) (s₀.gpr .r5)).writeW
    (saveAddr s₀ 72) (s₀.gpr .r6)).writeW (saveAddr s₀ 76) (s₀.gpr .r7)).writeW
    (saveAddr s₀ 80) (s₀.gpr .r8)).writeW (saveAddr s₀ 84) (s₀.gpr .r9)).writeW
    (saveAddr s₀ 88) (s₀.gpr .r10)).writeW (saveAddr s₀ 92) (s₀.gpr .r11)).writeW
    (saveAddr s₀ 96) (s₀.gpr .lr)

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr))) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.z = (s₀.gpr .r2 - 0 == 0) := by
  have o0 := hp.out_save (d := 64) (by omega); have o1 := hp.out_save (d := 68) (by omega)
  have o2 := hp.out_save (d := 72) (by omega); have o3 := hp.out_save (d := 76) (by omega)
  have o4 := hp.out_save (d := 80) (by omega); have o5 := hp.out_save (d := 84) (by omega)
  have o6 := hp.out_save (d := 88) (by omega); have o7 := hp.out_save (d := 92) (by omega)
  have o8 := hp.out_save (d := 96) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.store32, subFlags,
    o0, o1, o2, o3, o4, o5, o6, o7, o8, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_save hp]

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 112 → (scrR s₀).Contains (saveAddr s₀ d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (hp.saveAddr_eq (by omega))
  simp only [saveMem]
  have m := List.mem_singleton_self (scrR s₀)
  exact ((((((((Frame.refl _ _).writeW m _ (c 64 (by omega))).writeW m _ (c 68 (by omega))).writeW
    m _ (c 72 (by omega))).writeW m _ (c 76 (by omega))).writeW m _ (c 80 (by omega))).writeW
    m _ (c 84 (by omega))).writeW m _ (c 88 (by omega))).writeW m _ (c 92 (by omega))
    |>.writeW m _ (c 96 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩
  · rw [hm]; exact (saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame hp).readW (contains_sub (len := 20) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressArm.post s₀ s' := by
  have i0 := hp.in_save (d := 64) (by omega); have i1 := hp.in_save (d := 68) (by omega)
  have i2 := hp.in_save (d := 72) (by omega); have i3 := hp.in_save (d := 76) (by omega)
  have i4 := hp.in_save (d := 80) (by omega); have i5 := hp.in_save (d := 84) (by omega)
  have i6 := hp.in_save (d := 88) (by omega); have i7 := hp.in_save (d := 92) (by omega)
  have i8 := hp.in_save (d := 96) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5 i6 i7 i8
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hc.saved
  have hstate := hc.state
  have hr3 := hc.r3
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, State.load32, hr3,
    i0, i1, i2, i3, i4, i5, i6, i7, i8, ite_true, ite_false, g0, g1, g2, g3, g4, g5, g6, g7, g8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, hstate⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressArm.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .r2 - 0 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        r1 := by rw [hg]; simp [blkAddr]
        r2 := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified Arm.target Impl.Sha1.Arm.compress Proof.Sha1.compressArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha1.Arm
