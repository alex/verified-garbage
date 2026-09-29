import VerifiedGarbage.Proof.Sha512.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SHA-512 compression function on AArch64: the whole function

Untrusted: everything here is checked by Lean.
-/

/-!
## SHA-512: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are emitted with the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The contracts of the AArch64
implementations of the compression function and the streaming interface, in
terms of `Spec/Sha512.lean`.

The return address is in the link register `x30`, which the target's
calling convention requires to be preserved (`VG.AArch64.abiPreserved`), not
on the stack, so unlike on x86-64 no region needs to be kept disjoint from it.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 22])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read `blocks` (`128 * n` bytes) and read and write `state`
(64 bytes) and `scratch` (176 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers and `n` are public; the hash
value and the blocks are secret. -/
def compressAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let blocks : Region := ⟨s.gpr .x1, 128 * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, 176⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    stateAt s'.mem (s.gpr .x0) =
      compressBlocks (stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_<alg>_init(state: *mut [u8; 192])`, where `iv` is
the initial hash value of `<alg>` (`H0_384`, `H0_512`, `H0_512_224` or
`H0_512_256`): makes the streaming state at `state` represent the empty
message, hashed from `iv`.

The code may write `state` (192 bytes). The pointer is public. -/
def initAArch64 (iv : HashValue) : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    s.rd = [] ∧ s.wr = [state]
  post s s' := Repr iv s'.mem (s.gpr .x0) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 28])`:
if the streaming state at `state` represents a message `m` of `count` bytes
(modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `m` followed by the `len` bytes at `data`, from the same one.

The code may read `data` (`len` bytes) and read and write `state` (192
bytes) and `scratch` (224 bytes, whose contents on exit are unspecified).
These may not overlap each other. The pointers, `count` and `len` are public;
the state and the data are secret. -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 224⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    Repr iv s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for
`vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 28])`:
if the streaming state at `state` represents a message `m` of `count` bytes,
fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `m` from `iv` (64 bytes; `finalHash iv m`) to `out`. The
digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48, 28 or 32
bytes.

The code may read and write `state` (192 bytes, whose contents on exit are
unspecified), `out` (64 bytes) and `scratch` (224 bytes, whose contents on
exit are unspecified). These may not overlap each other. The pointers and
`count` are public; the state is secret. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 192⟩
    let out : Region := ⟨s.gpr .x2, 64⟩
    let scratch : Region := ⟨s.gpr .x3, 224⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch
  post s s' := ∀ iv m, Repr iv s.mem (s.gpr .x0) m → m.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .x2) 64 = finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha512


namespace VG.Proof.Sha512.AArch64

open VG VG.AArch64 VG.Impl.Sha512.AArch64
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * j)) 8 (p + BitVec.ofNat 64 (8 * k)) 8 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (8 * k)) v).readW (p + BitVec.ofNat 64 (8 * j)) 64 =
    m.readW (p + BitVec.ofNat 64 (8 * j)) 64 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev blR : Region := ⟨bp s₀, 128 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 176⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (128 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 128 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 8 * t) by simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 8 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x3 : s.gpr .x3 = scr s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

theorem preserved_sub : ∀ r ∈ preserved, r ∈ pubRegs := by decide

/-! ## One block -/

theorem load_eq : load = [
    .ldr .x .x4 .x0 (8 * 0), .ldr .x .x5 .x0 (8 * 1), .ldr .x .x6 .x0 (8 * 2),
    .ldr .x .x7 .x0 (8 * 3), .ldr .x .x8 .x0 (8 * 4), .ldr .x .x9 .x0 (8 * 5),
    .ldr .x .x10 .x0 (8 * 6), .ldr .x .x11 .x0 (8 * 7)] := by
  decide

theorem update_eq : update ++ advance = [
    .ldr .x .x12 .x0 (8 * 0), .ldr .x .x13 .x0 (8 * 1), .ldr .x .x14 .x0 (8 * 2),
    .ldr .x .x15 .x0 (8 * 3),
    .add .x .x4 .x4 .x12, .add .x .x5 .x5 .x13, .add .x .x6 .x6 .x14, .add .x .x7 .x7 .x15,
    .ldr .x .x12 .x0 (8 * (0 + 4)), .ldr .x .x13 .x0 (8 * (1 + 4)), .ldr .x .x14 .x0 (8 * (2 + 4)),
    .ldr .x .x15 .x0 (8 * (3 + 4)),
    .add .x .x8 .x8 .x12, .add .x .x9 .x9 .x13, .add .x .x10 .x10 .x14, .add .x .x11 .x11 .x15,
    .str .x .x4 .x0 (8 * 0), .str .x .x5 .x0 (8 * 1), .str .x .x6 .x0 (8 * 2),
    .str .x .x7 .x0 (8 * 3), .str .x .x8 .x0 (8 * 4), .str .x .x9 .x0 (8 * 5),
    .str .x .x10 .x0 (8 * 6), .str .x .x11 .x0 (8 * 7),
    .addImm .x .x1 .x1 128, .subImm .x .x2 .x2 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .x4 = v[0] ∧ s.gpr .x5 = v[1] ∧
    s.gpr .x6 = v[2] ∧ s.gpr .x7 = v[3] ∧
    s.gpr .x8 = v[4] ∧ s.gpr .x9 = v[5] ∧
    s.gpr .x10 = v[6] ∧ s.gpr .x11 = v[7] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hx0 : s.gpr .x0 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_x, isa, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hx0,
    h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Eight 64-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) v[0]).writeW
    (p + BitVec.ofNat 64 (8 * 1)) v[1]).writeW
    (p + BitVec.ofNat 64 (8 * 2)) v[2]).writeW
    (p + BitVec.ofNat 64 (8 * 3)) v[3]).writeW
    (p + BitVec.ofNat 64 (8 * 4)) v[4]).writeW
    (p + BitVec.ofNat 64 (8 * 5)) v[5]).writeW
    (p + BitVec.ofNat 64 (8 * 6)) v[6]).writeW
    (p + BitVec.ofNat 64 (8 * 7)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (8 * k)) (64 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * k)) 64 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .x1 = s.gpr .x1 + 128 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin (0 + 4) (by decide); have i5 := hin (1 + 4) (by decide)
  have i6 := hin (2 + 4) (by decide); have i7 := hin (3 + 4) (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH (0 + 4) (by decide); have m5 := hH (1 + 4) (by decide)
  have m6 := hH (2 + 4) (by decide); have m7 := hH (3 + 4) (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_ldr_x, exec_str_x, exec_add, exec_addImm_x, exec_subImm_x, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits, hx0,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  rotate_left 4
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})
  all_goals trivial

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev64 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev64_readW]
  simp only [blk, blockAt, parseBlock]
  have e : ∀ j : Nat, j < 7 → blkAddr s₀ i + BitVec.ofNat 64 (8 * t + j) + 1 =
      blkAddr s₀ i + BitVec.ofNat 64 (8 * t + (j + 1)) := fun j hj => by bv_omega
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (8 * t) = blkAddr s₀ i + BitVec.ofNat 64 (8 * t + 0) by rfl,
    e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega)]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 176⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.x0 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev64 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hx1₁ : s₁.gpr .x1 = blkAddr s₀ i := (hpub₁ .x1 (by decide)).trans hL.x1
  have hx3₁ : s₁.gpr .x3 = scr s₀ := (hpub₁ .x3 (by decide)).trans hL.x3
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hx1₁ hx3₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hx0₂ : s₂.gpr .x0 = st s₀ := by rw [pub₂ .x0 (by decide), hL.x0]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hx0₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hx1₃, hx2₃, hx0₃, hx3₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .x2 (by decide), hL.x2]
    have := (s₀.gpr .x2).isLt
    bv_omega
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hx0₃, hx0₂], by rw [hx3₃, pub₂ .x3 (by decide), hL.x3],
      fun r hr => by rw [hkept₃ r hr, pub₂ r (preserved_sub r hr), hL.kept r hr],
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
    · rw [hx1₃, pub₂ .x1 (by decide), hL.x1]
      simp only [blkAddr]
      bv_omega
    · rw [hx2₃, hx2]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
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
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 176⟩]

theorem compress_verified :
    Verified AArch64.target Impl.Sha512.AArch64.compress Proof.Sha512.compressAArch64 := by
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

end VG.Proof.Sha512.AArch64
