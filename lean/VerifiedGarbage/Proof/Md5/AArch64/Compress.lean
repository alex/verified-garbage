import VerifiedGarbage.Proof.Md5.AArch64.Rounds
import VerifiedGarbage.Proof.Md5.StateMem
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset

/-!
# MD5 compression function on AArch64: the whole function

Untrusted: everything here is checked by Lean.
-/

/-!
## MD5: the AArch64 contract

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the AArch64
implementations of the compression function and the streaming interface, in
terms of `Spec/Md5.lean`.

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

namespace VG.Proof.Md5

open Spec.Md5

open VG.AArch64 in
/-- AArch64 contract for
`vg_md5_compress(state: *mut [u32; 4], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 8])`:
updates the MD buffer at `state` with the `n` 64-byte blocks at `blocks`.

The code may read `blocks` (`64 * n` bytes) and read and write `state`
(16 bytes) and `scratch` (64 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the MD
buffer and the blocks are secret. -/
def compressAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 16⟩
    let blocks : Region := ⟨s.gpr .x1, 64 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, 64⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .x0) =
      compressBlocks (stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_md5_init(state: *mut [u8; 80])`: makes the
streaming state at `state` represent the empty message.

The code may write `state` (80 bytes). The pointer is public. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 80⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), then afterwards it represents `m` followed by the `len` bytes at
`data`.

The code may read `data` (`len` bytes) and read and write `state` (80
bytes) and `scratch` (112 bytes, whose contents on exit are unspecified).
These may not overlap each other, nor the 16 bytes below the stack pointer
(the frame saving `x30`), which do not wrap around. The pointers, `count` and
`len` are public; the state and the data are secret. -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 80⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 112⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    Repr s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16], scratch: *mut [u64; 14])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), writes the MD5 digest of `m` to `out`.

The code may read and write `state` (80 bytes, whose contents on exit are
unspecified), `out` (16 bytes) and `scratch` (112 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the 16 bytes
below the stack pointer (the frame saving `x30`), which do not wrap around.
The pointers and `count` are public; the state is secret. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 80⟩
    let out : Region := ⟨s.gpr .x2, 16⟩
    let scratch : Region := ⟨s.gpr .x3, 112⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Repr s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    bytesAt s'.mem (s.gpr .x2) 16 = Spec.Md5.hash m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Md5


namespace VG.Proof.Md5.AArch64

open VG VG.AArch64 VG.Impl.Md5.AArch64
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)

/-! The hash value in memory and offsets into regions (`Proof/Md5/StateMem.lean`). -/
export VG.Proof.Md5.StateMem (toNat_ofNat_lt contains_offset sub_offset word_sep readW_writeW_word
  stateAt_eq stateAt_get writeState stateAt_writeState)

/-- A 32-bit load reads four bytes, low-order byte first. -/
theorem readW_bytes (m : Mem) (a : Addr) :
    m.readW a 32 = (m (a + 1 + 1 + 1) ++ m (a + 1 + 1) ++ m (a + 1) ++ m a : BitVec 32) := by
  show (0#0 ++ m (a + 1 + 1 + 1) ++ m (a + 1 + 1) ++ m (a + 1) ++ m a).setWidth 32 = _
  simp only [BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero_length]
  split_ifs <;> first | omega | rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 16⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 64⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Md5.compressAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 4) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 4) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

theorem preserved_sub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-- The registers `load` does not write. -/
def loadKept : List Reg := [.x0, .x1, .x2, .x3] ++ preserved

theorem loadKept_sub : ∀ r ∈ loadKept, r ∈ pubRegs := by decide

/-! ## One block -/

theorem load_eq : load = [
    .ldr .w .x4 .x0 (4 * 0), .ldr .w .x5 .x0 (4 * 1), .ldr .w .x6 .x0 (4 * 2),
    .ldr .w .x7 .x0 (4 * 3),
    .movz .w .x14 (ones.extractLsb' 0 16) 0, .movk .w .x14 (ones.extractLsb' 16 16) 1] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .w .x12 .x0 (4 * 0), .ldr .w .x13 .x0 (4 * 1), .ldr .w .x14 .x0 (4 * 2),
    .ldr .w .x15 .x0 (4 * 3),
    .add .w .x4 .x4 .x12, .add .w .x5 .x5 .x13, .add .w .x6 .x6 .x14, .add .w .x7 .x7 .x15,
    .str .w .x4 .x0 (4 * 0), .str .w .x5 .x0 (4 * 1), .str .w .x6 .x0 (4 * 2),
    .str .w .x7 .x0 (4 * 3),
    .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0].setWidth 64 ∧ s.gpr .x5 = v[1].setWidth 64 ∧
    s.gpr .x6 = v[2].setWidth 64 ∧ s.gpr .x7 = v[3].setWidth 64 := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hx0 : s.gpr .x0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ s₁.gpr Ones = ones.setWidth 64 ∧
      (∀ r ∈ loadKept, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 4 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, Ones, runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w, exec_movz_w, exec_movk_w, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hx0,
    h0, h1, h2, h3, ite_true, ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 4 by decide), stateAt_get _ _ (show 1 < 4 by decide),
    stateAt_get _ _ (show 2 < 4 by decide), stateAt_get _ _ (show 3 < 4 by decide), movz_movk_w]
  simp (config := {decide := true}) [loadKept, preserved]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 4 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _ (c 3 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 4) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .x1 = s.gpr .x1 + 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      s'.gpr .x0 = s.gpr .x0 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 4 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 4 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_w, exec_str_w, exec_add, exec_addImm_x, exec_subImm_x, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx0, i0, i1, i2, i3, o0, o1, o2, o3,
    m0, m1, m2, m3, v0, v1, v2, v3, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp (config := {decide := true}))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i k : Nat) (hk : k < 16) :
    s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
  rw [readW_bytes]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * k) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 1) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 2) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 3) by
      bv_omega]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.x0 hL.rd hL.wr)
    fun s₁ ⟨hv₁, hones₁, hkept₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hX : ∀ k (hk : k < 16),
      s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * k)) 32 = blk s₀ i ⟨k, hk⟩ := by
    intro k hk
    rw [hm₁, hL.frame.readW (hp.blk_contains hi hk) (by simpa using hp.blk_st) (by decide)]
    exact blk_word i k hk
  have hx1₁ : s₁.gpr .x1 = blkAddr s₀ i := (hkept₁ .x1 (by decide)).trans hL.x1
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s₁ hx1₁ hones₁
    (fun k hk => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi hk) hX hv₁ 64 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have kept₂ : ∀ r ∈ loadKept, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r (loadKept_sub r hr), hkept₁ r hr]
  have hx0₂ : s₂.gpr .x0 = st s₀ := by rw [kept₂ .x0 (by decide), hL.x0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hx0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.mem, hm₁, stateAt_get _ _ hk]
  obtain ⟨hm₃, hx1₃, hx2₃, hx0₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [kept₂ .x2 (by decide), hL.x2]
    have := (s₀.gpr .x2).isLt
    bv_omega
  have hframe : Frame [stR s₀] s₀.mem s₃.mem := by
    rw [hm₃, hR.mem, hm₁]
    exact frame_writeState hL.frame _
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hx0₃, hx0₂],
      fun r hr => by
        rw [hkept₃ r hr, kept₂ r (by simp only [loadKept, List.mem_append]; exact .inr hr),
          hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .x .x2) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₃, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with x1 := ?_, x2 := ?_ }⟩
    · rw [hx1₃, kept₂ .x1 (by decide), hL.x1]
      simp only [blkAddr]
      bv_omega
    · rw [hx2₃, hx2]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Md5.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        x1 := by simp [blkAddr]
        x2 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Md5.AArch64.compress Proof.Md5.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Md5.AArch64
