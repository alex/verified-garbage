import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Impl.Sha3.X86
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Impl.Sha3.X86.Stream
import VerifiedGarbage.Proof.Sha3.Arith

section

/-!
# SHA-3: the x86 (32-bit) contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`), with
the arguments on the stack (cdecl).

The streaming functions call the permutation, each call pushing its two
arguments and storing its return address in the 12 bytes of stack below
the return address; they may overwrite their own arguments (`writeArgs`),
which the code does not do.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open X86 in
/-- x86 (32-bit) contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read the arguments (8 bytes above the return address), and read
and write `state` (200 bytes) and `scratch` (512 bytes, whose contents on
exit are unspecified), which may not overlap each other, the arguments or
the return address, or wrap around the end of the (32-bit) address space.
`esp` and the pointers are public; the state is secret. -/
def permuteX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let scratch : Region := ⟨(arg s 1).setWidth 64, 512⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) = keccakF (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_absorb(state, rate, pos, data, len,
scratch) -> eax`, whose arguments are on the stack: absorbs `data` into the
streaming state (`Repr`) and returns the new position in the block.

The code may read `data` (`len` bytes), and read and write `state` (200
bytes), `scratch` (640 bytes) and the arguments (24 bytes above the return
address). None of these may overlap another; none of the buffers may
overlap the return address or the 12 bytes of stack below it; nothing may
wrap around the end of the (32-bit) address space. `rate` is one of
`rates`, and `pos < rate`. `esp` and the arguments are public; the state and
the data are secret. -/
def absorbX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat < (arg s 1).toNat
  post s s' :=
    (∀ msg, Repr s.mem ((arg s 0).setWidth 64) (arg s 1).toNat msg →
      (arg s 2).toNat = msg.length % (arg s 1).toNat →
      Repr s'.mem ((arg s 0).setWidth 64) (arg s 1).toNat
        (msg ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)) ∧
    (s'.gpr .eax).toNat = ((arg s 2).toNat + (arg s 4).toNat) % (arg s 1).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_pad(state, rate, pos, suffix,
scratch)`, whose arguments are on the stack: absorbs the padding (with the
low byte of `suffix`) into the streaming state.

The code may read and write `state` (200 bytes), `scratch` (640 bytes) and
the arguments (20 bytes above the return address). None of these may
overlap another; neither buffer may overlap the return address or the 12
bytes of stack below it; nothing may wrap around the end of the (32-bit)
address space. `rate` is one of `rates`, and `pos < rate`. `esp` and the
arguments are public; the state is secret. -/
def padX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, scratch, args] ∧
    state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat < (arg s 1).toNat
  post s s' := ∀ msg, Repr s.mem ((arg s 0).setWidth 64) (arg s 1).toNat msg →
    (arg s 2).toNat = msg.length % (arg s 1).toNat →
    stateAt s'.mem ((arg s 0).setWidth 64) =
      absorb (arg s 1).toNat (pad (arg s 1).toNat ((arg s 3).setWidth 8) msg)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open X86 in
/-- x86 (32-bit) contract for `vg_keccak_squeeze(state, rate, pos, out,
outlen, scratch) -> eax`, whose arguments are on the stack: writes `outlen`
bytes of output from byte `pos` on to `out`, and returns the position after
them, leaving a state from which the output continues.

The code may read and write `state` (200 bytes), `out` (`outlen` bytes),
`scratch` (640 bytes) and the arguments (24 bytes above the return address).
None of these may overlap another; none of the buffers may overlap the
return address or the 12 bytes of stack below it; nothing may wrap around
the end of the (32-bit) address space. `rate` is one of `rates`, and
`pos ≤ rate`. `esp` and the arguments are public; the state is secret. -/
def squeezeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 200⟩
    let out : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 200 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 640 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    (arg s 1).toNat ∈ rates ∧ (arg s 2).toNat ≤ (arg s 1).toNat
  post s s' :=
    bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      squeezeFrom (arg s 1).toNat (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat
        (arg s 4).toNat ∧
    (s'.gpr .eax).toNat ≤ (arg s 1).toNat ∧
    ∀ d, squeezeFrom (arg s 1).toNat (stateAt s'.mem ((arg s 0).setWidth 64)) (s'.gpr .eax).toNat d =
      squeezeFrom (arg s 1).toNat (stateAt s.mem ((arg s 0).setWidth 64))
        ((arg s 2).toNat + (arg s 4).toNat) d
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Sha3

end

section

section

/-!
# SHA-3 on x86 (32-bit): lanes as pairs of words

The halves of the lanes (`half`), their rotations as the code computes them
(each half rotated, and their top bits exchanged), and weakest-precondition
rules for the macros of `VG.Impl.Sha3.X86` that load, combine, rotate and
store a lane in `(eax, edx)`, each proved once for any registers and offsets,
in continuation-passing style. The halves and the 64-bit words in memory are
those of the SHA-512 proofs (`Proof/Sha512/X86/Rounds.lean`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Sha3.X86 (sLo sHi ld2 xor2 st2 rot topMask)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_and hi_and lo_rotr hi_rotr)
open VG.Proof.Sha512.X86 (Only Pair rd64 write64 lo_rd64 hi_rd64 readSrc_mem wp_movS wp_xorS wp_andS
  wp_ror ea_of)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_store wp_mov)

abbrev Lane := Spec.Sha3.Lane

/-! ## Halves -/

/-- Half `h` of a lane: the low one for `h = 0`, else the high one. -/
def half (h : Nat) (v : Lane) : BitVec 32 := if h = 0 then lo v else hi v

theorem half_xor (h : Nat) (a b : Lane) : half h (a ^^^ b) = half h a ^^^ half h b := by
  unfold half; split
  · exact lo_xor a b
  · exact hi_xor a b

theorem half_and (h : Nat) (a b : Lane) : half h (a &&& b) = half h a &&& half h b := by
  unfold half; split
  · exact lo_and a b
  · exact hi_and a b

theorem half_ones (h : Nat) : half h (0xffffffffffffffff : Lane) = BitVec.allOnes 32 := by
  unfold half; split <;> rfl

theorem half_rd64 {h : Nat} (hh : h = 0 ∨ h = 4) (m : Mem) (b : BitVec 32) (o : Nat) :
    half h (rd64 m b o) = m.readW (addr b (o + h)) 32 := by
  rcases hh with rfl | rfl
  · exact lo_rd64 m b o
  · exact hi_rd64 m b o

theorem half_lo (v : Lane) : half 0 v = lo v := rfl

theorem half_hi (v : Lane) : half 4 v = hi v := rfl

/-! ## Rotations -/

/-- A rotation right by `0 < m < 32` of the halves `a` (low) and `b`: its low
half, as the code computes it. -/
theorem rot_half (a b : BitVec 32) {m : Nat} (h0 : 0 < m) (h : m < 32) :
    a >>> m ^^^ b <<< (32 - m) =
      a.rotateRight m ^^^ ((a.rotateRight m ^^^ b.rotateRight m) &&& topMask m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [topMask, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt h]
  by_cases hc : i < 32 - m
  · simp [hc, hi, show m + i < 32 by omega]
  · simp only [hc, hi, BitVec.getLsbD_of_ge a (m + i) (by omega), ite_false, decide_true,
      Bool.true_and, decide_false, Bool.not_false, show i - (32 - m) < 32 by omega]
    cases a.getLsbD (i - (32 - m)) <;> cases b.getLsbD (i - (32 - m)) <;> rfl

theorem lo_rotm (v : Lane) {m : Nat} (h0 : 0 < m) (h : m < 32) :
    lo (v.rotateRight m) = (lo v).rotateRight m ^^^
      (((lo v).rotateRight m ^^^ (hi v).rotateRight m) &&& topMask m) := by
  rw [lo_rotr _ h0 h, rot_half _ _ h0 h]

theorem hi_rotm (v : Lane) {m : Nat} (h0 : 0 < m) (h : m < 32) :
    hi (v.rotateRight m) = (hi v).rotateRight m ^^^
      (((lo v).rotateRight m ^^^ (hi v).rotateRight m) &&& topMask m) := by
  rw [hi_rotr _ h0 h, rot_half _ _ h0 h, BitVec.xor_comm ((hi v).rotateRight m) ((lo v).rotateRight m)]

theorem lo_rot32 (v : Lane) : lo (v.rotateRight 32) = hi v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi']

theorem hi_rot32 (v : Lane) : hi (v.rotateRight 32) = lo v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi', show 32 + i < 64 by omega, show ¬ 32 + i < 32 by omega]

theorem rotateRight_zero' (v : Lane) : v.rotateRight 0 = v := by
  ext i hi
  simp only [BitVec.getElem_rotateRight]
  split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _

theorem rotateRight_add (v : Lane) {a b : Nat} (h : a + b < 64) :
    (v.rotateRight a).rotateRight b = v.rotateRight (a + b) := by
  ext i hi
  simp only [BitVec.getElem_rotateRight, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show a < 64 by omega),
    Nat.mod_eq_of_lt (show b < 64 by omega)]
  split <;> split <;> split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _

/-- The lane `v`, its halves swapped if `sw`. -/
def swapIf (sw : Bool) (v : Lane) : Lane := if sw then v.rotateRight 32 else v

theorem swapIf_true (v : Lane) : swapIf true v = v.rotateRight 32 := rfl

theorem swapIf_false (v : Lane) : swapIf false v = v := rfl

theorem lo_swapIf (sw : Bool) (v : Lane) : lo (swapIf sw v) = half (sLo sw) v := by
  cases sw
  · rfl
  · exact lo_rot32 v

theorem hi_swapIf (sw : Bool) (v : Lane) : hi (swapIf sw v) = half (sHi sw) v := by
  cases sw
  · rfl
  · exact hi_rot32 v

theorem swapIf_xor (sw : Bool) (a b : Lane) : swapIf sw (a ^^^ b) = swapIf sw a ^^^ swapIf sw b := by
  cases sw
  · rfl
  · apply VG.Proof.Sha512.Word64.eq_of_lo_hi
    · simp only [swapIf, ite_true, lo_rot32, lo_xor, hi_xor]
    · simp only [swapIf, ite_true, hi_rot32, lo_xor, hi_xor]

theorem sLo_cases (sw : Bool) : sLo sw = 0 ∨ sLo sw = 4 := by cases sw <;> simp [sLo]

theorem sHi_cases (sw : Bool) : sHi sw = 0 ∨ sHi sw = 4 := by cases sw <;> simp [sHi]

/-! ## Single instructions -/

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 32} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]` -/
theorem wp_ldm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov d (.mem (at_ b o)) :: rest)) s Q :=
  wp_movS (readSrc_mem hb hin) k

/-- `xor d, [b + o]` -/
theorem wp_xorm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: rest)) s Q :=
  wp_xorS (readSrc_mem hb hin) k

/-- `and d, [b + o]` -/
theorem wp_andm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d &&& s.mem.readW (addr B o) 32) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .and d (.mem (at_ b o)) :: rest)) s Q :=
  wp_andS (readSrc_mem hb hin) k

/-- `mov [b + o], r` -/
theorem wp_stm {b r : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B) (hout : InRegions s.wr (addr B o) 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) (s.gpr r)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.store (at_ b o) r :: rest)) s Q :=
  wp_store (ea_of hb o) hout k

end

/-! ## Lanes in `(eax, edx)` -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- Both words of the lane at `[B + o]` may be read. -/
def Rd2 (s : State) (B : BitVec 32) (o : Nat) : Prop :=
  ∀ h, h = 0 ∨ h = 4 → InRegions (s.rd ++ s.wr) (addr B (o + h)) 4

theorem wp_ld2 {sw : Bool} {b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B) (hbe : b ≠ .eax)
    (hin : Rd2 s B o)
    (k : ∀ s', Only [.eax, .edx] s s' → Pair s' .eax .edx (swapIf sw (rd64 s.mem B o)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (ld2 sw b o ++ rest)) s Q := by
  simp only [ld2, List.cons_append, List.nil_append]
  refine wp_ldm hb (hin _ (sLo_cases sw)) fun s₁ u₁ => ?_
  refine wp_ldm (by rw [u₁.other _ hbe, hb]) (by rw [u₁.rd, u₁.wr]; exact hin _ (sHi_cases sw))
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr, lo_swapIf, half_rd64 (sLo_cases sw)]
  · rw [u₂.gpr, u₁.mem, hi_swapIf, half_rd64 (sHi_cases sw)]

theorem wp_xor2 {sw : Bool} {b : Reg} {B : BitVec 32} {o : Nat} {v : Lane} (hb : s.gpr b = B)
    (hbe : b ≠ .eax) (hin : Rd2 s B o) (hp : Pair s .eax .edx v)
    (k : ∀ s', Only [.eax, .edx] s s' → Pair s' .eax .edx (v ^^^ swapIf sw (rd64 s.mem B o)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xor2 sw b o ++ rest)) s Q := by
  simp only [xor2, List.cons_append, List.nil_append]
  refine wp_xorm hb (hin _ (sLo_cases sw)) fun s₁ u₁ => ?_
  refine wp_xorm (by rw [u₁.other _ hbe, hb]) (by rw [u₁.rd, u₁.wr]; exact hin _ (sHi_cases sw))
    fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr, lo_xor, lo_swapIf, half_rd64 (sLo_cases sw), hp.1]
  · rw [u₂.gpr, u₁.mem, u₁.other _ (by decide), hi_xor, hi_swapIf, half_rd64 (sHi_cases sw), hp.2]

theorem wp_rot {m : Nat} (hm : m < 32) {v : Lane} (hp : Pair s .eax .edx v)
    (k : ∀ s', Only [.eax, .edx, .ecx] s s' → Pair s' .eax .edx (v.rotateRight m) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (rot m ++ rest)) s Q := by
  unfold rot
  split
  · rename_i h0
    subst h0
    simp only [List.nil_append]
    exact k s (Only.refl _ _) (by rw [rotateRight_zero']; exact hp)
  · rename_i h0
    simp only [List.cons_append, List.nil_append]
    refine wp_ror ⟨by omega, by omega⟩ fun s₁ u₁ => wp_ror ⟨by omega, by omega⟩ fun s₂ u₂ =>
      wp_mov fun s₃ u₃ => wp_xorS rfl fun s₄ u₄ => wp_andS rfl fun s₅ u₅ =>
      wp_xorS rfl fun s₆ u₆ => wp_xorS rfl fun s₇ u₇ => k s₇ ?_ ⟨?_, ?_⟩
    · exact ((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
        (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇)
        |>.mono (by simp)
    all_goals
      have hA : s₂.gpr .eax = (lo v).rotateRight m := by
        rw [u₂.other .eax (by decide), u₁.gpr, hp.1]
      have hB : s₂.gpr .edx = (hi v).rotateRight m := by
        rw [u₂.gpr, u₁.other .edx (by decide), hp.2]
      have e5a : s₅.gpr .eax = (lo v).rotateRight m := by
        rw [u₅.other .eax (by decide), u₄.other .eax (by decide), u₃.other .eax (by decide), hA]
      have e5c : s₅.gpr .ecx = ((lo v).rotateRight m ^^^ (hi v).rotateRight m) &&& topMask m := by
        rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .edx (by decide), hA, hB]
    · rw [u₇.other .eax (by decide), u₆.gpr, e5a, e5c, lo_rotm _ (by omega) hm]
    · rw [u₇.gpr, u₆.other .edx (by decide), u₆.other .ecx (by decide), e5c, u₅.other .edx (by decide),
        u₄.other .edx (by decide), u₃.other .edx (by decide), hB, hi_rotm _ (by omega) hm]

/-- Both words of the lane at `[B + o]` may be written. -/
def Wr2 (s : State) (B : BitVec 32) (o : Nat) : Prop :=
  InRegions s.wr (addr B o) 4 ∧ InRegions s.wr (addr B (o + 4)) 4

theorem wp_st2 {b : Reg} {B : BitVec 32} {o : Nat} {v : Lane} (hb : s.gpr b = B)
    (hout : Wr2 s B o) (hp : Pair s .eax .edx v)
    (k : ∀ s', Mupd s s' (write64 s.mem B o v) → WP isa (.block rest) s' Q) :
    WP isa (.block (st2 b o ++ rest)) s Q := by
  simp only [st2, List.cons_append, List.nil_append]
  refine wp_stm hb hout.1 fun s₁ u₁ => ?_
  refine wp_stm (by rw [u₁.gpr, hb]) (by rw [u₁.wr]; exact hout.2)
    fun s₂ u₂ => k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

end

end VG.Proof.Sha3.X86

end

/-!
# Keccak-f[1600] on x86 (32-bit): one round

One round (`round src dst`) from the state at `src` to the state at `dst`,
lane by lane (`Proof.Sha3.out`), each lane a pair of 32-bit words, through the
work area of the scratch space (`C`, then `B`, and `D`), proved once for both
of the rounds of an iteration (`src`, `dst` being `esi`, `edi` or `edi`,
`esi`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86 VG.Impl.Sha3.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha512.Word64 (lo hi)
open VG.Impl.Sha3 (piSrc rhoOff)
open VG.Proof.Sha512.X86 (Only Pair Wrote rd64 write64 mem_rd Acc rd64_write64_self rd64_write64_ne
  rd64_frame wp_xorS)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_addi contains_addr)
open VG.Proof.Sha3 (C D B out outState)

abbrev KState := Spec.Sha3.State

/-! ## Registers -/

/-- The pointer registers of the rounds: `esi` (`state`) and `edi` (`scratch`). -/
def Ptr (r : Reg) : Prop := r = .esi ∨ r = .edi

theorem Ptr.ne {r : Reg} (h : Ptr r) : r ≠ .eax ∧ r ≠ .edx ∧ r ≠ .ecx ∧ r ≠ .ebp := by
  rcases h with rfl | rfl <;> decide

theorem nm1 {r a : Reg} (h : r ≠ a) : r ∉ [a] := by simp [h]
theorem nm3 {r a b c : Reg} (h₁ : r ≠ a) (h₂ : r ≠ b) (h₃ : r ≠ c) : r ∉ [a, b, c] := by
  simp [h₁, h₂, h₃]

/-! ## Regions -/

theorem addr_zero (b : BitVec 32) : addr b 0 = b.setWidth 64 := by simp [addr]

/-- The `n` bytes at offset `o` of a region at `b` are within its part at offset `a`. -/
theorem sub_contains {b : BitVec 32} {N a k o n : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hak : a + k ≤ N)
    (h1 : a ≤ o) (h2 : o + n ≤ a + k) (hn : 0 < n) : (⟨addr b a, k⟩ : Region).Contains (addr b o) n := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have hE : (b.setWidth 64).toNat = b.toNat := VG.Proof.Sha256.X86.Stream.addr_toNat b
  generalize b.setWidth 64 = E at *
  bv_omega

/-- Two parts of a region at `b` that do not overlap. -/
theorem sub_disj {b : BitVec 32} {N a n c k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (ha : a + n ≤ N)
    (hc : c + k ≤ N) (hn : 0 < n) (hk : 0 < k) (h : a + n ≤ c ∨ c + k ≤ a) :
    Region.Disjoint ⟨addr b a, n⟩ ⟨addr b c, k⟩ := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Proof.Sha3.off_disjoint _ (by omega) (by omega) h

/-- The region of `n` bytes at a 32-bit pointer. -/
abbrev reg32 (b : BitVec 32) (n : Nat) : Region := ⟨b.setWidth 64, n⟩

/-- The work area of the scratch space at `W`: `C` and then `B`, and `D`. -/
abbrev workR (W : BitVec 32) : Region := ⟨addr W 408, 80⟩

theorem work_contains {W : BitVec 32} (hfit : W.toNat + 512 ≤ 2 ^ 32) {o : Nat} (h1 : 408 ≤ o)
    (h2 : o + 4 ≤ 488) : (workR W).Contains (addr W o) 4 :=
  sub_contains (N := 512) hfit (by omega) h1 (by omega) (by omega)

theorem reg_contains {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) {o : Nat} (h : o + 4 ≤ N) :
    (reg32 b N).Contains (addr b o) 4 :=
  contains_addr h (by omega) hfit

theorem Frame.write64' {rs : List Region} {m m' : Mem} (h : Frame rs m m') {R : Region} (hr : R ∈ rs)
    {b : BitVec 32} {o : Nat} (hc0 : R.Contains (addr b o) 4) (hc4 : R.Contains (addr b (o + 4)) 4)
    (v : Lane) : Frame rs m (write64 m' b o v) :=
  (h.writeW hr _ hc0).writeW hr _ hc4

theorem rd64_frame' {rs : List Region} {m m' : Mem} (h : Frame rs m m') {R : Region} {b : BitVec 32}
    {o : Nat} (hc0 : R.Contains (addr b o) 4) (hc4 : R.Contains (addr b (o + 4)) 4)
    (hd : ∀ r ∈ rs, R.Disjoint r) : rd64 m' b o = rd64 m b o := by
  simp only [rd64]
  rw [h.readW hc4 hd (by decide), h.readW hc0 hd (by decide)]

/-- A word of the work area is unchanged by writes outside it. -/
theorem work_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {W : BitVec 32}
    (hfit : W.toNat + 512 ≤ 2 ^ 32) {o : Nat} (h1 : 408 ≤ o) (h2 : o + 8 ≤ 488)
    (hd : ∀ r ∈ rs, (workR W).Disjoint r) : rd64 m' W o = rd64 m W o :=
  rd64_frame' h (work_contains hfit h1 (by omega)) (work_contains hfit (by omega) (by omega)) hd

/-! ## States in memory -/

/-- The state at `b` holds `K`, lane `i` as the pair of words at `b + 8i`. -/
def Lanes32 (m : Mem) (b : BitVec 32) (K : KState) : Prop := ∀ i < 25, rd64 m b (8 * i) = K[i]!

theorem Lanes32.frame {m m' : Mem} {b : BitVec 32} {K : KState} (hK : Lanes32 m b K) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (reg32 b 200).Disjoint r) (hfit : b.toNat + 200 ≤ 2 ^ 32) :
    Lanes32 m' b K := fun i hi => by
  rw [rd64_frame hf hd hfit (by omega)]; exact hK i hi

/-- Where a round reads and writes: the state at `S`, the scratch space at
`W` (its work area), the round constant at `P`, and the state at `Dd`,
which overlaps none of the others. -/
structure Env (wr : List Region) (S Dd W P : BitVec 32) : Prop where
  fitS : S.toNat + 200 ≤ 2 ^ 32
  fitD : Dd.toNat + 200 ≤ 2 ^ 32
  fitW : W.toNat + 512 ≤ 2 ^ 32
  fitP : P.toNat + 8 ≤ 2 ^ 32
  accS : Acc wr S 200
  accD : Acc wr Dd 200
  accW : Acc wr W 512
  accP : Acc wr P 8
  sd : (reg32 S 200).Disjoint (reg32 Dd 200)
  sw : (reg32 S 200).Disjoint (workR W)
  dw : (reg32 Dd 200).Disjoint (workR W)
  pd : (reg32 P 8).Disjoint (reg32 Dd 200)
  pw : (reg32 P 8).Disjoint (workR W)

theorem Env.rd2W {wr : List Region} {S Dd W P : BitVec 32} (E : Env wr S Dd W P) {o : Nat} (ho : o + 8 ≤ 512)
    {s : State} (hw : s.wr = wr) : Rd2 s W o := fun h hh =>
  mem_rd (by rw [hw]; exact E.accW _ (by rcases hh with rfl | rfl <;> omega))

theorem Env.wr2W {wr : List Region} {S Dd W P : BitVec 32} (E : Env wr S Dd W P) {o : Nat} (ho : o + 8 ≤ 512)
    {s : State} (hw : s.wr = wr) : Wr2 s W o :=
  ⟨by rw [hw]; exact E.accW _ (by omega), by rw [hw]; exact E.accW _ (by omega)⟩

theorem cOff_lt (x : Nat) (hx : x < 5) : 408 ≤ cOff x ∧ cOff x + 8 ≤ 448 := by simp only [cOff]; omega

theorem dOff_lt (x : Nat) (hx : x < 5) : 448 ≤ dOff x ∧ dOff x + 8 ≤ 488 := by simp only [dOff]; omega

/-! ## θ -/

theorem colHalf_ok {src : Reg} (hsrc : Ptr src) {x h : Nat} (hx : x < 5) (hh : h = 0 ∨ h = 4)
    {S W : BitVec 32} {K : KState} (s : State) (hS : s.gpr src = S) (hW : s.gpr .edi = W)
    (aS : Acc s.wr S 200) (aW : Acc s.wr W 512) (hK : Lanes32 s.mem S K) :
    WP isa (.block (colHalf src x h)) s fun s' =>
      Wrote [.eax] s s' (s.mem.writeW (addr W (cOff x + h)) (half h (C K x))) := by
  have rS : ∀ i < 25, InRegions (s.rd ++ s.wr) (addr S (8 * i + h)) 4 := fun i hi =>
    mem_rd (aS _ (by rcases hh with rfl | rfl <;> omega))
  have ve : ∀ i < 25, s.mem.readW (addr S (8 * i + h)) 32 = half h K[i]! := fun i hi => by
    rw [← hK i hi, half_rd64 hh]
  have se := hsrc.ne.1
  unfold colHalf
  refine wp_ldm hS (rS x (by omega)) fun s₁ u₁ => ?_
  refine wp_xorm (by rw [u₁.other _ se, hS]) (by rw [u₁.rd, u₁.wr]; exact rS (x + 5) (by omega))
    fun s₂ u₂ => ?_
  have U₂ := Upd.trans u₁ u₂
  refine wp_xorm (by rw [U₂.other _ se, hS]) (by rw [U₂.rd, U₂.wr]; exact rS (x + 10) (by omega))
    fun s₃ u₃ => ?_
  have U₃ := Upd.trans U₂ u₃
  refine wp_xorm (by rw [U₃.other _ se, hS]) (by rw [U₃.rd, U₃.wr]; exact rS (x + 15) (by omega))
    fun s₄ u₄ => ?_
  have U₄ := Upd.trans U₃ u₄
  refine wp_xorm (by rw [U₄.other _ se, hS]) (by rw [U₄.rd, U₄.wr]; exact rS (x + 20) (by omega))
    fun s₅ u₅ => ?_
  have U₅ := Upd.trans U₄ u₅
  refine wp_stm (by rw [U₅.other _ (by decide), hW])
    (by rw [U₅.wr]; exact aW _ (by simp only [cOff]; rcases hh with rfl | rfl <;> omega))
    fun s₆ u₆ => WP.block_nil ⟨fun r hr => ?_, ?_, by rw [u₆.rd, U₅.rd], by rw [u₆.wr, U₅.wr]⟩
  · rw [u₆.gpr, U₅.other r (by simpa using hr)]
  · rw [u₆.mem, U₅.mem, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, U₄.mem, U₃.mem, U₂.mem, u₁.mem,
      ve x (by omega), ve (x + 5) (by omega), ve (x + 10) (by omega), ve (x + 15) (by omega),
      ve (x + 20) (by omega), C, half_xor, half_xor, half_xor, half_xor]

theorem column_ok {src : Reg} (hsrc : Ptr src) {x : Nat} (hx : x < 5) {S Dd W P : BitVec 32}
    {K : KState} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S) (hW : s.gpr .edi = W)
    (hK : Lanes32 s.mem S K) :
    WP isa (.block (column src x)) s fun s' => Wrote [.eax] s s' (write64 s.mem W (cOff x) (C K x)) := by
  have hc := cOff_lt x hx
  unfold column
  rw [WP.block_append_iff]
  refine WP.mono (colHalf_ok hsrc hx (.inl rfl) s hS hW E.accS E.accW hK) fun s₁ w₁ => ?_
  have hf : Frame [workR W] s.mem s₁.mem := by
    rw [w₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (work_contains E.fitW hc.1 (by omega))
  refine WP.mono (colHalf_ok hsrc hx (.inr rfl) s₁ (by rw [w₁.gpr _ (nm1 hsrc.ne.1), hS])
    (by rw [w₁.gpr _ (nm1 (by decide)), hW]) (by rw [w₁.wr]; exact E.accS) (by rw [w₁.wr]; exact E.accW)
    (hK.frame hf (by simpa using E.sw) E.fitS)) fun s₂ w₂ =>
      ⟨fun r hr => by rw [w₂.gpr r hr, w₁.gpr r hr], ?_, w₂.rd.trans w₁.rd, w₂.wr.trans w₁.wr⟩
  rw [w₂.mem, w₁.mem, half_lo, half_hi]; rfl

/-- After the first `k` columns. -/
structure ColInv (s₀ : State) (K : KState) (W : BitVec 32) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR W] s₀.mem s.mem
  cs : ∀ x < k, rd64 s.mem W (cOff x) = C K x

theorem columns_ok {src : Reg} (hsrc : Ptr src) {S Dd W P : BitVec 32} {K : KState} (s₀ : State)
    (E : Env s₀.wr S Dd W P) (hS : s₀.gpr src = S) (hW : s₀.gpr .edi = W) (hK : Lanes32 s₀.mem S K) :
    WP isa (.block ((List.range 5).flatMap (column src))) s₀ (ColInv s₀ K W 5) := by
  refine wp_range_flatMap (M := isa) (ColInv s₀ K W) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hc := cOff_lt x hx
  refine WP.mono (column_ok hsrc hx s (hI.wr ▸ E) (by rw [hI.gpr _ (nm1 hsrc.ne.1), hS])
    (by rw [hI.gpr _ (nm1 (by decide)), hW]) (hK.frame hI.frame (by simpa using E.sw) E.fitS))
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun x' hx' => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (work_contains E.fitW hc.1 (by omega))
      (work_contains E.fitW (by omega) (by omega)) _
  · rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by have := E.fitW; omega)
    · have := cOff_lt x' (by omega)
      rw [rd64_write64_ne _ _ (by have := E.fitW; omega) (by have := E.fitW; omega)
        (by simp only [cOff]; omega)]
      exact hI.cs x' (by omega)

/-! ## D -/

theorem dcol_ok (x : Nat) (hx : x < 5) {S Dd W P : BitVec 32} {K : KState} (s : State)
    (E : Env s.wr S Dd W P) (hW : s.gpr .edi = W) (hc : ∀ x' < 5, rd64 s.mem W (cOff x') = C K x') :
    WP isa (.block (dcol x)) s fun s' =>
      Wrote [.eax, .edx, .ecx] s s' (write64 s.mem W (dOff x) (D K x)) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4 : (x + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  have c1 := cOff_lt _ h1
  have c4 := cOff_lt _ h4
  have d := dOff_lt x hx
  unfold dcol
  refine wp_ld2 hW (by decide) (E.rd2W (by omega) rfl) fun s₁ o₁ p₁ => ?_
  refine wp_rot (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O₂ : Only [.eax, .edx, .ecx] s s₂ := (o₁.trans o₂).mono (by simp)
  refine wp_xor2 (sw := false) (by rw [O₂.gpr _ (by decide), hW]) (by decide)
    (E.rd2W (by omega) O₂.wr) p₂ fun s₃ o₃ p₃ => ?_
  have O₃ : Only [.eax, .edx, .ecx] s s₃ := (O₂.trans o₃).mono (by simp)
  rw [← List.append_nil (st2 _ _)]
  refine wp_st2 (by rw [O₃.gpr _ (by decide), hW]) (E.wr2W (by omega) O₃.wr) p₃ fun s₄ u₄ =>
    WP.block_nil ⟨fun r hr => by rw [u₄.gpr, O₃.gpr r hr], ?_, by rw [u₄.rd, O₃.rd],
      by rw [u₄.wr, O₃.wr]⟩
  rw [u₄.mem, O₃.mem, O₂.mem, hc _ h1, hc _ h4, swapIf_true, swapIf_false,
    rotateRight_add _ (show 32 + 31 < 64 by decide)]
  rfl

/-- After the first `k` of the `D[x]`. -/
structure DInv (s₀ : State) (K : KState) (W : BitVec 32) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .edx, .ecx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR W] s₀.mem s.mem
  cs : ∀ x < 5, rd64 s.mem W (cOff x) = C K x
  ds : ∀ x < k, rd64 s.mem W (dOff x) = D K x

theorem dcols_ok {S Dd W P : BitVec 32} {K : KState} (s₀ : State) (E : Env s₀.wr S Dd W P)
    (hW : s₀.gpr .edi = W) (hc : ∀ x < 5, rd64 s₀.mem W (cOff x) = C K x) :
    WP isa (.block ((List.range 5).flatMap dcol)) s₀ (DInv s₀ K W 5) := by
  have fW := E.fitW
  refine wp_range_flatMap (M := isa) (DInv s₀ K W) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, hc, fun _ h => absurd h (by omega)⟩
  have d := dOff_lt x hx
  refine WP.mono (dcol_ok x hx s (hI.wr ▸ E) (by rw [hI.gpr _ (by decide), hW]) hI.cs)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (work_contains fW (by omega) (by omega))
      (work_contains fW (by omega) (by omega)) _
  · have := cOff_lt x' hx'
    rw [w.mem, rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
    exact hI.cs x' hx'
  · rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by have := dOff_lt x' (by omega); omega)
        (by simp only [dOff]; omega)]
      exact hI.ds x' (by omega)

/-! ## A plane -/

theorem rhoOff_ne32 : ∀ j < 25, rhoOff j ≠ 32 := by decide

/-- ρ's rotation, as the code does it: the halves swapped (`swp`), then a
rotation by less than 32 (`rotAmt`). -/
theorem rho_rot (v : Lane) {j : Nat} (hj : j < 25) :
    (swapIf (swp j) v).rotateRight (rotAmt j) = Proof.Sha3.rotl v (rhoOff j) := by
  have h64 := Proof.Sha3.rhoOff_lt j hj
  have h32 := rhoOff_ne32 j hj
  simp only [swp, rotAmt, Proof.Sha3.rotl]
  generalize rhoOff j = r at *
  by_cases h0 : r = 0
  · subst h0; simp [swapIf, rotateRight_zero']
  · by_cases hl : r < 32
    · simp only [h0, hl, ite_false, ite_true, decide_true, Bool.and_true, swapIf,
        show (0 < r) = True from eq_true (by omega), decide_true]
      rw [rotateRight_add _ (by omega), show 32 + (32 - r) = 64 - r by omega]
    · simp only [h0, hl, ite_false, swapIf, show decide (0 < r) = true from decide_eq_true (by omega),
        Bool.true_and, decide_false, Bool.false_eq_true]

theorem rotAmt_lt {j : Nat} (hj : j < 25) : rotAmt j < 32 := by
  have := rhoOff_ne32 j hj
  have := Proof.Sha3.rhoOff_lt j hj
  unfold rotAmt
  split
  · omega
  · split <;> omega

theorem laneB_ok (x y : Nat) (hx : x < 5) (_hy : y < 5) {src : Reg} (hsrc : Ptr src)
    {S Dd W P : BitVec 32} {K : KState} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S)
    (hW : s.gpr .edi = W) (hK : Lanes32 s.mem S K) (hD : ∀ x' < 5, rd64 s.mem W (dOff x') = D K x') :
    WP isa (.block (laneB src x y)) s fun s' =>
      Wrote [.eax, .edx, .ecx] s s' (write64 s.mem W (cOff x) (B K x y)) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  have hk : (x + 3 * y) % 5 < 5 := Nat.mod_lt _ (by omega)
  have d := dOff_lt _ hk
  have c := cOff_lt x hx
  unfold laneB
  refine wp_ld2 hS hsrc.ne.1 (fun h hh => mem_rd (E.accS _ (by rcases hh with rfl | rfl <;> omega)))
    fun s₁ o₁ p₁ => ?_
  refine wp_xor2 (by rw [o₁.gpr _ (by decide), hW]) (by decide) (E.rd2W (by omega) o₁.wr) p₁
    fun s₂ o₂ p₂ => ?_
  have O₂ : Only [.eax, .edx] s s₂ := (o₁.trans o₂).mono (by simp)
  refine wp_rot (rotAmt_lt hj) p₂ fun s₃ o₃ p₃ => ?_
  have O₃ : Only [.eax, .edx, .ecx] s s₃ := (O₂.trans o₃).mono (by simp)
  rw [← List.append_nil (st2 _ _)]
  refine wp_st2 (by rw [O₃.gpr _ (by decide), hW]) (E.wr2W (by omega) O₃.wr) p₃ fun s₄ u₄ =>
    WP.block_nil ⟨fun r hr => by rw [u₄.gpr, O₃.gpr r hr], ?_, by rw [u₄.rd, O₃.rd],
      by rw [u₄.wr, O₃.wr]⟩
  rw [u₄.mem, O₃.mem, o₁.mem, hK _ hj, hD _ hk, ← swapIf_xor, rho_rot _ hj, B]

/-- After the first `k` lanes `B[x]` of plane `y`. -/
structure BInv (s₀ : State) (K : KState) (W : BitVec 32) (y k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .edx, .ecx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR W] s₀.mem s.mem
  ds : ∀ x < 5, rd64 s.mem W (dOff x) = D K x
  bs : ∀ x < k, rd64 s.mem W (cOff x) = B K x y

theorem laneBs_ok (y : Nat) (hy : y < 5) {src : Reg} (hsrc : Ptr src) {S Dd W P : BitVec 32}
    {K : KState} (s₀ : State) (E : Env s₀.wr S Dd W P) (hS : s₀.gpr src = S) (hW : s₀.gpr .edi = W)
    (hK : Lanes32 s₀.mem S K) (hD : ∀ x < 5, rd64 s₀.mem W (dOff x) = D K x) :
    WP isa (.block ((List.range 5).flatMap fun x => laneB src x y)) s₀ (BInv s₀ K W y 5) := by
  have fW := E.fitW
  refine wp_range_flatMap (M := isa) (BInv s₀ K W y) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, hD, fun _ h => absurd h (by omega)⟩
  have c := cOff_lt x hx
  obtain ⟨se, sd, sc, -⟩ := hsrc.ne
  refine WP.mono (laneB_ok x y hx hy hsrc s (hI.wr ▸ E) (by rw [hI.gpr _ (nm3 se sd sc), hS])
    (by rw [hI.gpr _ (by decide), hW]) (hK.frame hI.frame (by simpa using E.sw) E.fitS) hI.ds)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun x' hx' => ?_, fun x' hx' => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (work_contains fW c.1 (by omega))
      (work_contains fW (by omega) (by omega)) _
  · have := dOff_lt x' hx'
    rw [w.mem, rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
    exact hI.ds x' hx'
  · rw [w.mem]
    by_cases e : x' = x
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by have := cOff_lt x' (by omega); omega)
        (by simp only [cOff]; omega)]
      exact hI.bs x' (by omega)

/-- Half `h` of lane `(x, y)` of the output. -/
theorem chiHalf_ok (x y h : Nat) (hx : x < 5) (hy : y < 5) (hh : h = 0 ∨ h = 4) {dst : Reg}
    (hdst : Ptr dst) {S Dd W P : BitVec 32} {K : KState} {rc : Lane} (s : State)
    (E : Env s.wr S Dd W P) (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P)
    (hb : ∀ x' < 5, rd64 s.mem W (cOff x') = B K x' y) (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (chiHalf dst x y h)) s fun s' =>
      Wrote [.eax] s s' (s.mem.writeW (addr Dd (8 * (x + 5 * y) + h)) (half h (out K rc x y))) := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have c0 := cOff_lt x hx
  have c1 := cOff_lt _ h1
  have c2 := cOff_lt _ h2
  have hB : ∀ x' < 5, s.mem.readW (addr W (cOff x' + h)) 32 = half h (B K x' y) := fun x' hx' => by
    rw [← hb x' hx', half_rd64 hh]
  have rW : ∀ x' < 5, InRegions (s.rd ++ s.wr) (addr W (cOff x' + h)) 4 := fun x' hx' =>
    mem_rd (E.accW _ (by have := cOff_lt x' hx'; rcases hh with rfl | rfl <;> omega))
  unfold chiHalf
  simp only [List.cons_append, List.nil_append]
  refine wp_ldm hW (rW _ h1) fun s₁ u₁ => ?_
  refine wp_xorS rfl fun s₂ u₂ => ?_
  have U₂ := Upd.trans u₁ u₂
  refine wp_andm (by rw [U₂.other _ (by decide), hW]) (by rw [U₂.rd, U₂.wr]; exact rW _ h2)
    fun s₃ u₃ => ?_
  have U₃ := Upd.trans U₂ u₃
  refine wp_xorm (by rw [U₃.other _ (by decide), hW]) (by rw [U₃.rd, U₃.wr]; exact rW _ hx)
    fun s₄ u₄ => ?_
  have U₄ := Upd.trans U₃ u₄
  have v₄ : s₄.gpr .eax = half h ((B K ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B K ((x + 2) % 5) y ^^^
      B K x y) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, U₃.mem, U₂.mem, hB _ h1, hB _ h2, hB _ hx, half_xor,
      half_and, half_xor, half_ones]
  have fin : ∀ s₅ : State, Upd s s₅ .eax (half h (out K rc x y)) →
      WP isa (.block [.store (at_ dst (8 * (x + 5 * y) + h)) .eax]) s₅ fun s' =>
        Wrote [.eax] s s' (s.mem.writeW (addr Dd (8 * (x + 5 * y) + h)) (half h (out K rc x y))) :=
    fun s₅ U₅ => wp_stm (by rw [U₅.other _ hdst.ne.1, hd])
      (by rw [U₅.wr]; exact E.accD _ (by rcases hh with rfl | rfl <;> omega))
      fun s₆ u₆ => WP.block_nil ⟨fun r hr => by rw [u₆.gpr, U₅.other r (by simpa using hr)],
        by rw [u₆.mem, U₅.mem, U₅.gpr], by rw [u₆.rd, U₅.rd], by rw [u₆.wr, U₅.wr]⟩
  by_cases h0 : x = 0 ∧ y = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    simp only [List.cons_append, List.nil_append]
    have hr : s.mem.readW (addr P h) 32 = half h rc := by rw [← hrc, half_rd64 hh, Nat.zero_add]
    refine wp_xorm (by rw [U₄.other _ (by decide), hP]) (by
      rw [U₄.rd, U₄.wr]; exact mem_rd (E.accP _ (by rcases hh with rfl | rfl <;> omega))) fun s₅ u₅ => ?_
    refine fin s₅ ⟨?_, (Upd.trans U₄ u₅).other, (Upd.trans U₄ u₅).mem, (Upd.trans U₄ u₅).rd, (Upd.trans U₄ u₅).wr⟩
    rw [u₅.gpr, v₄, U₄.mem, hr, ← half_xor, out]
    simp only [h0, and_self, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    simp only [List.nil_append]
    refine fin s₄ ⟨?_, U₄.other, U₄.mem, U₄.rd, U₄.wr⟩
    rw [v₄, out]
    simp only [h0, ite_false]

theorem chi_ok (x y : Nat) (hx : x < 5) (hy : y < 5) {dst : Reg} (hdst : Ptr dst)
    {S Dd W P : BitVec 32} {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd W P)
    (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P)
    (hb : ∀ x' < 5, rd64 s.mem W (cOff x') = B K x' y) (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (chi dst x y)) s fun s' =>
      Wrote [.eax] s s' (write64 s.mem Dd (8 * (x + 5 * y)) (out K rc x y)) := by
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  unfold chi
  rw [WP.block_append_iff]
  refine WP.mono (chiHalf_ok x y 0 hx hy (.inl rfl) hdst s E hd hW hP hb hrc) fun s₁ w₁ => ?_
  have hf : Frame [reg32 Dd 200] s.mem s₁.mem := by
    rw [w₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (reg_contains E.fitD (by omega))
  have g : ∀ r, r ≠ .eax → s₁.gpr r = s.gpr r := fun r hr => w₁.gpr r (nm1 hr)
  refine WP.mono (chiHalf_ok x y 4 hx hy (.inr rfl) hdst (rc := rc) s₁ (w₁.wr ▸ E) (by rw [g _ hdst.ne.1, hd])
    (by rw [g _ (by decide), hW]) (by rw [g _ (by decide), hP])
    (fun x' hx' => by
      have := cOff_lt x' hx'
      rw [work_frame hf E.fitW this.1 (by omega) (by simpa using E.dw.symm)]; exact hb x' hx')
    (by rw [rd64_frame hf (by simpa using E.pd) E.fitP (by omega)]; exact hrc)) fun s₂ w₂ =>
      ⟨fun r hr => by rw [w₂.gpr r hr, w₁.gpr r hr], ?_, w₂.rd.trans w₁.rd, w₂.wr.trans w₁.wr⟩
  rw [w₂.mem, w₁.mem, half_lo, half_hi]; rfl

/-- After `k` lanes of plane `y` of the output. -/
structure ChiInv (s₀ : State) (K : KState) (rc : Lane) (Dd W : BitVec 32) (y k : Nat) (s : State) :
    Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [reg32 Dd 200] s₀.mem s.mem
  lanes : ∀ j < 5 * y + k, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem chis_ok (y : Nat) (hy : y < 5) {dst : Reg} (hdst : Ptr dst) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd W P) (hd : s₀.gpr dst = Dd)
    (hW : s₀.gpr .edi = W) (hP : s₀.gpr .ebp = P) (hb : ∀ x < 5, rd64 s₀.mem W (cOff x) = B K x y)
    (hrc : rd64 s₀.mem P 0 = rc) (hl : ∀ j < 5 * y, rd64 s₀.mem Dd (8 * j) = out K rc (j % 5) (j / 5)) :
    WP isa (.block ((List.range 5).flatMap fun x => chi dst x y)) s₀ (ChiInv s₀ K rc Dd W y 5) := by
  have fD := E.fitD
  refine wp_range_flatMap (M := isa) (ChiInv s₀ K rc Dd W y) (fun x s hx hI => ?_) 5 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => hl j (by omega)⟩
  have ho : 8 * (x + 5 * y) + 8 ≤ 200 := by omega
  refine WP.mono (chi_ok x y hx hy hdst (rc := rc) s (hI.wr ▸ E) (by rw [hI.gpr _ (nm1 hdst.ne.1), hd])
    (by rw [hI.gpr _ (by decide), hW]) (by rw [hI.gpr _ (by decide), hP])
    (fun x' hx' => by
      have := cOff_lt x' hx'
      rw [work_frame hI.frame E.fitW this.1 (by omega) (by simpa using E.dw.symm)]; exact hb x' hx')
    (by rw [rd64_frame hI.frame (by simpa using E.pd) E.fitP (by omega)]; exact hrc))
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun j hj => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _) (reg_contains fD (by omega))
      (reg_contains fD (by omega)) _
  · rw [w.mem]
    by_cases e : j = x + 5 * y
    · subst e
      rw [rd64_write64_self _ _ (by omega), show (x + 5 * y) % 5 = x by omega,
        show (x + 5 * y) / 5 = y by omega]
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.lanes j (by omega)

/-- After the first `y` planes of the output. -/
structure PInv (s₀ : State) (K : KState) (rc : Lane) (Dd W : BitVec 32) (y : Nat) (s : State) :
    Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .edx, .ecx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [reg32 Dd 200, workR W] s₀.mem s.mem
  ds : ∀ x < 5, rd64 s.mem W (dOff x) = D K x
  lanes : ∀ j < 5 * y, rd64 s.mem Dd (8 * j) = out K rc (j % 5) (j / 5)

theorem planes_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s₀ : State) (E : Env s₀.wr S Dd W P) (hS : s₀.gpr src = S)
    (hd : s₀.gpr dst = Dd) (hW : s₀.gpr .edi = W) (hP : s₀.gpr .ebp = P) (hK : Lanes32 s₀.mem S K)
    (hrc : rd64 s₀.mem P 0 = rc) (s : State) (hs : PInv s₀ K rc Dd W 0 s) :
    WP isa (.block ((List.range 5).flatMap (plane src dst))) s (PInv s₀ K rc Dd W 5) := by
  have fD := E.fitD
  refine wp_range_flatMap (M := isa) (PInv s₀ K rc Dd W) (fun y s hy hI => ?_) 5 (Nat.le_refl _) s hs
  unfold plane
  rw [WP.block_append_iff]
  obtain ⟨se, sd, sc, -⟩ := hsrc.ne
  obtain ⟨de, dd, dc, -⟩ := hdst.ne
  have E' : Env s.wr S Dd W P := hI.wr ▸ E
  refine WP.mono (laneBs_ok y hy hsrc s E' (by rw [hI.gpr _ (nm3 se sd sc), hS])
    (by rw [hI.gpr _ (by decide), hW]) (hK.frame hI.frame (by simpa using ⟨E.sd, E.sw⟩) E.fitS) hI.ds)
    fun s₁ b₁ => ?_
  have E₁ : Env s₁.wr S Dd W P := b₁.wr ▸ E'
  have f₁ : Frame [reg32 Dd 200, workR W] s₀.mem s₁.mem :=
    hI.frame.trans (b₁.frame.mono (by simp))
  refine WP.mono (chis_ok y hy hdst (rc := rc) s₁ E₁ (by rw [b₁.gpr _ (nm3 de dd dc), hI.gpr _ (nm3 de dd dc), hd])
    (by rw [b₁.gpr _ (by decide), hI.gpr _ (by decide), hW])
    (by rw [b₁.gpr _ (by decide), hI.gpr _ (by decide), hP]) b₁.bs
    (by rw [rd64_frame f₁ (by simpa using ⟨E.pd, E.pw⟩) E.fitP (by omega)]; exact hrc)
    (fun j hj => by
      rw [rd64_frame b₁.frame (by simpa using E.dw) fD (by omega)]; exact hI.lanes j hj))
    fun s₂ c₂ => ⟨fun r hr => ?_, by rw [c₂.rd, b₁.rd, hI.rd], by rw [c₂.wr, b₁.wr, hI.wr],
      f₁.trans (c₂.frame.mono (by simp)), fun x hx => ?_, fun j hj => c₂.lanes j (by omega)⟩
  · have ⟨a, b, c⟩ : r ≠ .eax ∧ r ≠ .edx ∧ r ≠ .ecx := by simpa using hr
    rw [c₂.gpr r (nm1 a), b₁.gpr r hr, hI.gpr r hr]
  · have := dOff_lt x hx
    rw [work_frame c₂.frame E.fitW (by omega) this.2 (by simpa using E.dw.symm)]; exact b₁.ds x hx

/-! ## The round -/

theorem round_ok {src dst : Reg} (hsrc : Ptr src) (hdst : Ptr dst) {S Dd W P : BitVec 32}
    {K : KState} {rc : Lane} (s : State) (E : Env s.wr S Dd W P) (hS : s.gpr src = S)
    (hd : s.gpr dst = Dd) (hW : s.gpr .edi = W) (hP : s.gpr .ebp = P) (hK : Lanes32 s.mem S K)
    (hrc : rd64 s.mem P 0 = rc) :
    WP isa (.block (round src dst)) s fun s' =>
      Lanes32 s'.mem Dd (outState K rc) ∧ Frame [reg32 Dd 200, workR W] s.mem s'.mem ∧
      s'.gpr .ebp = P + 8 ∧ (∀ r, r ∉ [Reg.eax, .edx, .ecx, .ebp] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold round
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok hsrc s E hS hW hK) fun s₁ c₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dcols_ok s₁ (c₁.wr ▸ E) (by rw [c₁.gpr _ (by decide), hW]) c₁.cs) fun s₂ d₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (planes_ok hsrc hdst s E hS hd hW hP hK hrc s₂ ⟨fun r hr => ?_,
    by rw [d₂.rd, c₁.rd], by rw [d₂.wr, c₁.wr], (c₁.frame.trans d₂.frame).mono (by simp), d₂.ds,
    fun j hj => absurd hj (by omega)⟩) fun s₃ p₃ => ?_
  · have a : r ≠ .eax := by rintro rfl; simp at hr
    rw [d₂.gpr r hr, c₁.gpr r (nm1 a)]
  refine wp_addi fun s₄ u₄ => WP.block_nil ⟨fun i hi => ?_, by rw [u₄.mem]; exact p₃.frame,
    by rw [u₄.gpr, p₃.gpr _ (by decide), hP], fun r hr => ?_, by rw [u₄.rd, p₃.rd],
    by rw [u₄.wr, p₃.wr]⟩
  · rw [u₄.mem, p₃.lanes i (by omega)]
    simp [outState, hi]
  · have ⟨a, b, c, e⟩ : r ≠ .eax ∧ r ≠ .edx ∧ r ≠ .ecx ∧ r ≠ .ebp := by simpa using hr
    rw [u₄.other r e, p₃.gpr r (nm3 a b c)]

end VG.Proof.Sha3.X86

end

/-!
# Keccak-f[1600] on x86 (32-bit): the whole function

The prologue loads the arguments, saves the callee-saved registers and stores
the round constants in the scratch space; each iteration of the loop runs two
rounds (`round_ok`), from the state to the second state in the scratch space
and back; the epilogue restores the registers.
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86 VG.Impl.Sha3.X86
open VG.Impl.Sha512.X86 (at_)
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha512.X86 (Only Wrote rd64 write64 mem_rd Acc rd64_write64_self rd64_write64_ne
  rd64_frame)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_addi wp_sub wp_cmpi eval_ne sub_beq
  addr_toNat)
open VG.Proof.Sha3 (outState_eq foldl_succ)
open VG.Proof.Sha512.Word64 (lo hi readW64)

/-! ## Addresses -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := arg s₀ 0
abbrev scp : BitVec 32 := arg s₀ 1
abbrev A₀ : KState := stateAt s₀.mem ((stp s₀).setWidth 64)
abbrev stR : Region := reg32 (stp s₀) 200
abbrev scR : Region := reg32 (scp s₀) 512
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : BitVec 32 := if r % 2 = 0 then stp s₀ else scp s₀
def oth (r : Nat) : BitVec 32 := if r % 2 = 0 then scp s₀ else stp s₀

/-- The address of the constant of round `r`. -/
abbrev rcp (r : Nat) : BitVec 32 := scp s₀ + BitVec.ofNat 32 (200 + 8 * r)

end

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | omega | rfl

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = stp s₀ ∧ oth s₀ r = scp s₀) ∨ (cur s₀ r = scp s₀ ∧ oth s₀ r = stp s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem cur_even (s₀ : State) (t : Nat) : cur s₀ (2 * t) = stp s₀ ∧ oth s₀ (2 * t) = scp s₀ := by
  simp only [cur, oth]; split
  · exact ⟨rfl, rfl⟩
  · omega

theorem cur_odd (s₀ : State) (t : Nat) : cur s₀ (2 * t + 1) = scp s₀ ∧ oth s₀ (2 * t + 1) = stp s₀ := by
  simp only [cur, oth]; split
  · omega
  · exact ⟨rfl, rfl⟩

theorem addr_add (b : BitVec 32) (a o : Nat) : addr (b + BitVec.ofNat 32 a) o = addr b (a + o) := by
  simp only [addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rcp_succ (s₀ : State) (r : Nat) : rcp s₀ r + 8 = rcp s₀ (r + 1) := by
  simp only [rcp]
  bv_omega

theorem rd64_rcp (m : Mem) (s₀ : State) (r : Nat) :
    rd64 m (rcp s₀ r) 0 = rd64 m (scp s₀) (200 + 8 * r) := by
  simp only [rd64, rcp, addr_add, Nat.zero_add, Nat.add_zero]

theorem reg32_eq (b : BitVec 32) (n : Nat) : reg32 b n = ⟨addr b 0, n⟩ := by rw [addr_zero]

/-- A part of a region at `b`. -/
theorem sub32 {b : BitVec 32} {N a k : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (h : a + k ≤ N) (hk : 0 < k) :
    Region.Sub ⟨addr b a, k⟩ (reg32 b N) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [addr_eq (by omega)] at hx
  have hE := addr_toNat b
  generalize b.setWidth 64 = E at *
  bv_omega

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  disj : (stR s₀).Disjoint (scR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_sc : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_sc : (retR s₀).Disjoint (scR s₀)
  fitS : (stp s₀).toNat + 200 ≤ 2 ^ 32
  fitC : (scp s₀).toNat + 512 ≤ 2 ^ 32
  fitSp : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem accS : Acc s₀.wr (stp s₀) 200 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [h.wr]; simp) h.fitS

theorem accC : Acc s₀.wr (scp s₀) 512 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [h.wr]; simp) h.fitC

theorem accC200 : Acc s₀.wr (scp s₀) 200 := fun o ho => h.accC o (by omega)

/-- A part of the scratch space beyond the second state, and the state being written. -/
theorem sc_dst {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {d n : Nat} (hd₀ : 200 ≤ d)
    (hd : d + n ≤ 512) (hn : 0 < n) : Region.Disjoint ⟨addr (scp s₀) d, n⟩ (reg32 Dd 200) := by
  rcases hD with rfl | rfl
  · exact h.disj.symm.sub_left (sub32 h.fitC hd hn)
  · rw [reg32_eq]; exact sub_disj h.fitC hd (by omega) hn (by omega) (.inr hd₀)

/-- A part of the scratch space outside its work area. -/
theorem sc_work {d n : Nat} (hd : d + n ≤ 512) (hn : 0 < n) (hs : d + n ≤ 408 ∨ 488 ≤ d) :
    Region.Disjoint ⟨addr (scp s₀) d, n⟩ (workR (scp s₀)) :=
  sub_disj h.fitC hd (by omega) hn (by omega) hs

theorem st_work : (stR s₀).Disjoint (workR (scp s₀)) :=
  h.disj.sub_right (sub32 h.fitC (by omega) (by omega))

theorem state_work {S : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) :
    (reg32 S 200).Disjoint (workR (scp s₀)) := by
  rcases hS with rfl | rfl
  · exact h.st_work
  · rw [reg32_eq]; exact h.sc_work (by omega) (by omega) (.inl (by omega))

theorem st_sc200 : (stR s₀).Disjoint (reg32 (scp s₀) 200) :=
  h.disj.sub_right (Region.sub_prefix (by omega))

theorem env_of {S Dd : BitVec 32} (hS : S = stp s₀ ∨ S = scp s₀) (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    (hSD : (reg32 S 200).Disjoint (reg32 Dd 200)) {r : Nat} (hr : r < 24) :
    Env s₀.wr S Dd (scp s₀) (rcp s₀ r) := by
  have fS := h.fitS
  have fC := h.fitC
  have hP : (rcp s₀ r).toNat = (scp s₀).toNat + (200 + 8 * r) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 200 + 8 * r) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, fC, by omega, ?_, ?_, h.accC, fun o ho => ?_, hSD, h.state_work hS,
    h.state_work hD, ?_, ?_⟩
  · rcases hS with rfl | rfl <;> omega
  · rcases hD with rfl | rfl <;> omega
  · rcases hS with rfl | rfl
    · exact h.accS
    · exact h.accC200
  · rcases hD with rfl | rfl
    · exact h.accS
    · exact h.accC200
  · rw [addr_add]; exact h.accC _ (by omega)
  · show Region.Disjoint ⟨addr (scp s₀) (200 + 8 * r), 8⟩ _
    exact h.sc_dst hD (by omega) (by omega) (by omega)
  · show Region.Disjoint ⟨addr (scp s₀) (200 + 8 * r), 8⟩ _
    exact h.sc_work (by omega) (by omega) (.inl (by omega))

theorem env {r : Nat} (hr : r < 24) : Env s₀.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := by
  rcases cur_cases s₀ r with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.env_of (.inl rfl) (.inr rfl) h.st_sc200 hr
  · exact h.env_of (.inr rfl) (.inl rfl) h.st_sc200.symm hr

/-- Words of the scratch space that a round does not write. -/
theorem keep_round {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {m m' : Mem}
    (hf : Frame [reg32 Dd 200, workR (scp s₀)] m m') {d : Nat} (hd : 200 ≤ d) (hd' : d + 4 ≤ 408) :
    m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (scp s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.sc_dst hD hd (by omega) (by decide)
  · exact h.sc_work (by omega) (by decide) (.inl hd')

end Pre

/-! ## What the scratch space holds -/

/-- The round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, rd64 m (scp s₀) (200 + 8 * j) = RC j

/-- The saved registers. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scp s₀)) s₀.gpr saved

theorem saved_ok : ∀ p ∈ saved, 392 ≤ p.2 ∧ p.2 + 4 ≤ 404 := by decide

theorem saved_fits : Spill.Fits 404 saved := by decide

theorem Aux.keep {s₀ : State} {m m' : Mem} (ha : Aux s₀ m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32) :
    Aux s₀ m' := fun j hj => by
  simp only [rd64]
  rw [hk _ (by omega) (by omega), hk _ (by omega) (by omega)]
  exact ha j hj

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 392 ≤ d → d + 4 ≤ 404 → m'.readW (addr (scp s₀) d) 32 = m.readW (addr (scp s₀) d) 32) :
    Saved s₀ m' :=
  hs.of_readW fun p hp => hk _ (saved_ok p hp).1 (saved_ok p hp).2

/-! ## The state in memory -/

theorem stateAt_get {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) (m : Mem) {i : Nat} (hi : i < 25) :
    (stateAt m (b.setWidth 64))[i] = rd64 m b (8 * i) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, show b.setWidth 64 + BitVec.ofNat 64 (8 * i) + 4 =
      b.setWidth 64 + BitVec.ofNat 64 (8 * i + 4) by bv_omega,
    ← addr_eq (by omega), ← addr_eq (by omega)]

theorem stateAt_eq {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) {m : Mem} {K : KState}
    (h : Lanes32 m b K) : stateAt m (b.setWidth 64) = K := by
  apply Vector.ext
  intro i hi
  rw [stateAt_get hfit m hi, h i hi]
  exact getElem!_pos K i hi

/-! ## The rounds -/

/-- The loop's invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  esi : s.gpr .esi = stp s₀
  edi : s.gpr .edi = scp s₀
  ebp : s.gpr .ebp = rcp s₀ r
  keep : ∀ q, q ∉ [Reg.eax, .edx, .ecx, .esi, .edi, .ebp] → s.gpr q = s₀.gpr q
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes32 s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  saved : Saved s₀ s.mem
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {src dst : Reg} (hsrc : Ptr src)
    (hdst : Ptr dst) {s : State} (hL : LInv s₀ r s) (h0 : s.gpr src = cur s₀ r)
    (hd : s.gpr dst = oth s₀ r) : WP isa (.block (round src dst)) s (LInv s₀ (r + 1)) := by
  have hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := (cur_cases s₀ r).symm.imp (·.2) (·.2)
  have E : Env s.wr (cur s₀ r) (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env hr
  refine WP.mono (round_ok hsrc hdst (rc := RC r) s E h0 hd hL.edi hL.ebp hL.state
    (by rw [rd64_rcp]; exact hL.aux r hr)) fun s' ⟨hl, hf, hbp, hq, hrd, hwr⟩ => ?_
  have g : ∀ q ∈ [Reg.esi, .edi], s'.gpr q = s.gpr q := fun q hq' => hq q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl <;> decide)
  refine ⟨by rw [g _ (by simp), hL.esi], by rw [g _ (by simp), hL.edi], by rw [hbp, rcp_succ],
    fun q hq' => ?_, hrd.trans hL.rd, hwr.trans hL.wr, ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega),
    hL.saved.keep fun d hd hd' => hp.keep_round hD hf (by omega) (by omega), ?_⟩
  · have ⟨a, b, c, _, _, e⟩ : q ≠ .eax ∧ q ≠ .edx ∧ q ≠ .ecx ∧ q ≠ .esi ∧ q ≠ .edi ∧ q ≠ .ebp := by
      simpa using hq'
    rw [hq q (by simp [a, b, c, e]), hL.keep q hq']
  · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · rcases hD with e | e <;> rw [e]
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨scR s₀, by simp, sub32 hp.fitC (by omega) (by omega)⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 12) {s : State} (hL : LInv s₀ (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega) (src := .esi) (dst := .edi) (.inl rfl)
    (.inr rfl) hL (by rw [hL.esi, (cur_even s₀ t).1]) (by rw [hL.edi, (cur_even s₀ t).2]))
    fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega) (src := .edi) (dst := .esi) (.inr rfl)
    (.inl rfl) h₁ (by rw [h₁.edi, (cur_odd s₀ t).1]) (by rw [h₁.esi, (cur_odd s₀ t).2]))
    fun s₂ h₂ => ?_
  have h₂' : LInv s₀ (2 * (t + 1)) s₂ := by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega]; exact h₂
  refine wp_mov fun s₃ u₃ => wp_sub fun s₄ u₄ _ => wp_cmpi fun s₅ u₅ _ hz => WP.block_nil ?_
  have hT : s₄.gpr .eax = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .edi (by decide), h₂'.ebp, h₂'.edi]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    VG.Proof.Sha256.X86.Stream.sub_beq (by omega) (by omega)] at hz
  have g : ∀ q, q ≠ .eax → s₅.gpr q = s₂.gpr q := fun q hq => by
    rw [u₅.gpr, u₄.other q hq, u₃.other q hq]
  have hs₅ : LInv s₀ (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g _ (by decide), h₂'.esi]
    · rw [g _ (by decide), h₂'.edi]
    · rw [g _ (by decide), h₂'.ebp]
    · rw [g _ (by rintro rfl; simp at hq), h₂'.keep q hq]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.saved
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.frame
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega)]; rfl, by omega, hs₅⟩

/-! ## The prologue -/

/-- Round constant `k`, stored in the scratch space at `edi`. -/
theorem rcStore_ok (k : Nat) (_hk : k < 24) {W : BitVec 32} (s : State) (hW : s.gpr .edi = W)
    (hin : Wr2 s W (200 + 8 * k)) :
    WP isa (.block (rcStore k)) s fun s' =>
      Wrote [.eax] s s' (write64 s.mem W (200 + 8 * k) (RC k)) := by
  unfold rcStore
  refine wp_movi fun s₁ u₁ => wp_stm (by rw [u₁.other _ (by decide), hW]) (by rw [u₁.wr]; exact hin.1)
    fun s₂ u₂ => ?_
  refine wp_movi fun s₃ u₃ => ?_
  rw [show 204 + 8 * k = 200 + 8 * k + 4 by omega]
  refine wp_stm (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hW])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin.2) fun s₄ u₄ =>
      WP.block_nil ⟨fun r hr => ?_, ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  · have hr' : r ≠ .eax := by simpa using hr
    rw [u₄.gpr, u₃.other r hr', u₂.gpr, u₁.other r hr']
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl

/-- During the stores of the round constants. -/
structure RcInv (s₀ s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax] → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨addr (scp s₀) 200, 192⟩] s₁.mem s.mem
  rcs : ∀ j < k, rd64 s.mem (scp s₀) (200 + 8 * j) = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s₁ : State) (hW : s₁.gpr .edi = scp s₀) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 24).flatMap rcStore)) s₁ (RcInv s₀ s₁ 24) := by
  have fC := hp.fitC
  refine wp_range_flatMap (M := isa) (RcInv s₀ s₁) (fun k s hk hI => ?_) 24 (Nat.le_refl _) s₁
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (rcStore_ok k hk s (by rw [hI.gpr _ (by decide), hW])
    ⟨by rw [hI.wr, hwr]; exact hp.accC _ (by omega), by rw [hI.wr, hwr]; exact hp.accC _ (by omega)⟩)
    fun s' w => ⟨fun r hr => by rw [w.gpr r hr, hI.gpr r hr], w.rd.trans hI.rd, w.wr.trans hI.wr, ?_,
      fun j hj => ?_⟩
  · rw [w.mem]
    exact Frame.write64' hI.frame (List.mem_singleton_self _)
      (sub_contains fC (by omega) (by omega) (by omega) (by omega))
      (sub_contains fC (by omega) (by omega) (by omega) (by omega)) _
  · rw [w.mem]
    by_cases e : j = k
    · subst e; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact hI.rcs j (by omega)

theorem prologue_eq : prologue = (.mov .eax (.mem (at_ .esp 8)) :: .mov .ecx (.mem (at_ .esp 4)) ::
    (Spill.saveCode .eax saved ++ ([.mov .edi (.reg .eax), .mov .esi (.reg .ecx)] : List Instr))) ++
    ((List.range 24).flatMap rcStore ++
      ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 200)] : List Instr)) := rfl

theorem arg_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 2) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  have := hp.fitSp
  show (⟨addr (s₀.gpr .esp) 4, 8⟩ : Region).Contains _ _
  exact sub_contains (N := 12) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  have fC := hp.fitC
  have fS := hp.fitS
  rw [prologue_eq, WP.block_append_iff]
  refine wp_ldm (B := s₀.gpr .esp) rfl (arg_in hp (i := 1) (by omega)) fun s₁ u₁ => ?_
  refine wp_ldm (B := s₀.gpr .esp) (by rw [u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact arg_in hp (i := 0) (by omega)) fun s₂ u₂ => ?_
  have e1 : s₂.gpr .eax = scp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  have e2 : s₂.gpr .ecx = stp s₀ := by rw [u₂.gpr, u₁.mem]; rfl
  have w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have sin : ∀ (t : State), t.wr = s₀.wr → ∀ d, 392 ≤ d → d + 4 ≤ 404 →
      InRegions t.wr (addr (scp s₀) d) 4 := fun t ht d _ _ => by rw [ht]; exact hp.accC _ (by omega)
  refine Spill.save_ok saved (fun p h => by
    rw [e1]; exact sin _ w₂ _ (saved_ok p h).1 (saved_ok p h).2) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have g₅ : ∀ r, s₅.gpr r = s₂.gpr r := fun r => by rw [u₅.gpr]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₂.other r h2, u₁.other r h1]
  have hW₇ : s₇.gpr .edi = scp s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e1]
  have w₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, w₂]
  -- The saved registers, and the memory the saves changed.
  have hm₇ : s₇.mem = Spill.saveMem s₀.mem (addr (scp s₀)) s₀.gpr saved := by
    rw [u₇.mem, u₆.mem, u₅.mem, e1, u₂.mem, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => g₂ _ (by revert p h; decide) (by revert p h; decide)
  have fr₇ : Frame [⟨addr (scp s₀) 392, 12⟩] s₀.mem s₇.mem := by
    rw [hm₇]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      sub_contains fC (by omega) (saved_ok p h).1 (saved_ok p h).2 (by omega)
  have sv₇ : Saved s₀ s₇.mem := by
    rw [hm₇]; exact Spill.saveMem_saved_addr _ _ saved_fits (by omega)
  have hwr₇ := w₇
  -- The round constants.
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₇ hW₇ w₇) fun s₈ h₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ => WP.block_nil ?_
  have g₈ : ∀ r, r ≠ .eax → s₈.gpr r = s₇.gpr r := fun r hr => h₈.gpr r (by simpa using hr)
  have keep : ∀ d, 392 ≤ d → d + 4 ≤ 404 →
      s₁₀.mem.readW (addr (scp s₀) d) 32 = s₇.mem.readW (addr (scp s₀) d) 32 := fun d h1 h2 => by
    rw [u₁₀.mem, u₉.mem]
    exact h₈.frame.readW (Region.contains_self _ _) (by
      simpa using sub_disj fC (by omega) (by omega) (by omega) (by omega) (.inr h1)) (by decide)
  have fr₁₀ : Frame [⟨addr (scp s₀) 392, 12⟩, ⟨addr (scp s₀) 200, 192⟩] s₀.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem]
    exact (fr₇.mono (by simp)).trans (h₈.frame.mono (by simp))
  refine ⟨?_, ?_, ?_, fun q hq => ?_, by rw [u₁₀.rd, u₉.rd, h₈.rd, u₇.rd, u₆.rd, u₅.rd,
    u₂.rd, u₁.rd], by rw [u₁₀.wr, u₉.wr, h₈.wr, w₇], fun i hi => ?_, ?_,
    sv₇.keep fun d h1 h2 => keep d h1 h2, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), g₈ _ (by decide), u₇.gpr, u₆.other _ (by decide),
      g₅, e2]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), g₈ _ (by decide), hW₇]
  · rw [u₁₀.gpr, u₉.gpr, g₈ _ (by decide), hW₇]; rfl
  · have ⟨a, _, c', d', e', f⟩ : q ≠ .eax ∧ q ≠ .edx ∧ q ≠ .ecx ∧ q ≠ .esi ∧ q ≠ .edi ∧ q ≠ .ebp := by
      simpa using hq
    rw [u₁₀.other q f, u₉.other q f, g₈ q a, u₇.other q d', u₆.other q e', g₅,
      g₂ q a c']
  · -- The state is untouched.
    have hc : cur s₀ 0 = stp s₀ := by simp [cur]
    rw [hc, rd64_frame fr₁₀ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.disj.sub_right (sub32 fC (by omega) (by omega))
      · exact hp.disj.sub_right (sub32 fC (by omega) (by omega))) fS (by omega),
      ← stateAt_get fS _ hi]
    simp only [List.range_zero, List.foldl_nil]
    exact (getElem!_pos _ i hi).symm
  · rw [u₁₀.mem, u₉.mem]; exact h₈.rcs
  · refine fr₁₀.sub fun R hR => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨scR s₀, by simp, sub32 fC (by omega) (by omega)⟩
    · exact ⟨scR s₀, by simp, sub32 fC (by omega) (by omega)⟩

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block restore) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.permuteX86.post s₀ s' := by
  have fC := hp.fitC
  have hin : ∀ d, 392 ≤ d → d + 4 ≤ 404 → InRegions (s.rd ++ s.wr) (addr (scp s₀) d) 4 :=
    fun d _ _ => mem_rd (by rw [hL.wr]; exact hp.accC _ (by omega))
  rw [show restore = Spill.restoreCode .edi ([(.esi, 392), (.ebp, 400)] ++ [(.edi, 396)]) ++ [] from rfl]
  refine Spill.restoreBase_ok _ (by decide)
    (fun p h => have hb := saved_ok p (by revert p h; decide); by rw [hL.edi]; exact hin _ hb.1 hb.2)
    (by rw [hL.edi]; exact hL.saved.sub (by decide)) fun s₃ r₃ => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases h : r ∈ ([(.esi, 392), (.ebp, 400)] ++ [(.edi, 396)] : Spill.Slots).map Prod.fst
    · exact r₃.regs r h
    · rw [r₃.other r h, hL.keep r (by revert h; revert hr; revert r; decide)]
  · rw [r₃.mem]
    exact hL.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_sc⟩) (by decide)
  · show stateAt s₃.mem ((stp s₀).setWidth 64) = keccakF (A₀ s₀)
    rw [r₃.mem]
    have hc : cur s₀ 24 = stp s₀ := by simp [cur]
    exact stateAt_eq hp.fitS (hc ▸ hL.state)

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.permuteX86.post s₀ s' := by
  unfold permute
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 24) ?_ fun s₂ h₂ => restore_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ t, n = 12 - t ∧ t < 12 ∧ LInv s₀ (2 * t) s
  refine WP.loop (M := isa) Inv (fun n s ⟨t, hn, ht, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (body_ok hp ht hL) fun s' h => ?_
  rcases h with ⟨he, hL'⟩ | ⟨he, ht', hL'⟩
  · exact .inl ⟨he, hL'⟩
  · exact .inr ⟨he, 12 - (t + 1), by omega, t + 1, rfl, ht', hL'⟩

/-! ## Constant time -/

/-- The constant-time analysis's taint without the round constants that the
prologue stores at `[200, 392)` of the scratch space: public, but no
address or branch depends on them, and the kernel checks the analysis much
faster without them (`taint_decide_weak`). -/
def dropRC (τ : VG.X86.Taint.T) : VG.X86.Taint.T :=
  { τ with slots := τ.slots.filter fun sl => !(200 ≤ sl.2.1 && sl.2.1 < 392) }

/-- The taint analysis starts with `esp` public, and the words holding
`state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 512], argLen := 12,
    argBases := [(4, 0), (8, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.fitS; have hsc := hp.fitC; have hs := hp.fitSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_sc hp.arg_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.permuteX86.pre s₁)
    (h₂ : Proof.Sha3.permuteX86.pre s₂) (hpub : Proof.Sha3.permuteX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scR, stp, scp, a0, a1]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.fitSp h4 hk, VG.X86.Taint.argByte_eq hp₂.fitSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def satMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x4004, 8⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem sat_pre : Proof.Sha3.permuteX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha3.permuteX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem permute_verified : Verified X86.target permute Proof.Sha3.permuteX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub)
      (by taint_decide_weak dropRC),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sha3.X86

section

section

/-!
# SHA-3 on x86 (32-bit): calling the permutation

A call of `vg_keccak_f1600` in a frame of its two arguments (`permuteCall`),
from its proof of `Verified` (`WP.callWith`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_nosp : NoSp Impl.Sha3.X86.permute := NoSp.of_all (by decide +kernel)

theorem permute_stack : stackUse Impl.Sha3.X86.permute = 0 := by decide +kernel

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-- Calling `vg_keccak_f1600(st, scr)` on the state at `S` with the first 512
bytes of the scratch space at `C` (of 640 bytes): the call uses the 12 bytes
below `esp` (`E`), for its arguments and return address. -/
theorem permuteCall_ok {st scr : Reg} (hst : st ≠ .esp) (hscr : scr ≠ .esp) {s : State}
    {S C E : BitVec 32} (hesp : s.gpr .esp = E) (hS : s.gpr st = S) (hC : s.gpr scr = C)
    (hE : 12 ≤ E.toNat) (fS : S.toNat + 200 ≤ 2 ^ 32) (fC : C.toNat + 512 ≤ 2 ^ 32)
    (d : (reg32 S 200).Disjoint (reg32 C 512)) (dS : (below E 12).Disjoint (reg32 S 200))
    (dC : (below E 12).Disjoint (reg32 C 512)) (wS : reg32 S 200 ∈ s.wr) (wC : reg32 C 640 ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 S 200, reg32 C 512, below E 12] s.mem s'.mem →
      stateAt s'.mem (S.setWidth 64) = keccakF (stateAt s.mem (S.setWidth 64)) → Q s') :
    WP isa (Impl.Sha3.X86.Stream.permuteCall st scr) s Q := by
  have fit : 4 * [scr, st].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ [scr, st] := by simp [Ne.symm hst, Ne.symm hscr]
  have a0 : arg (pushed [scr, st] s).callEntry 0 = S := by
    rw [callEntry_arg fit hrs (by simp)]; exact hS
  have a1 : arg (pushed [scr, st] s).callEntry 1 = C := by
    rw [callEntry_arg fit hrs (by simp)]; exact hC
  have eA : argAddr (pushed [scr, st] s).callEntry 0 = (E - BitVec.ofNat 32 8).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed [scr, st] s).callEntry.gpr .esp = E - BitVec.ofNat 32 12 := by
    rw [callEntry_esp', hesp]; rfl
  have b8 : Region.Sub (below E 8) (below E 12) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below E 12) := by
    have := below_inner (sp := E) (a := 4) (b := 12) (k := 8) (by omega) hE
    rw [show E - BitVec.ofNat 32 12 = E - BitVec.ofNat 32 8 - BitVec.ofNat 32 4 by bv_omega]
    exact this
  refine WP.callWith (k := Proof.Sha3.permuteX86) permute_verified.1 permute_nosp (by simp) hrs
    (by rw [permute_stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨argAddr (pushed [scr, st] s).callEntry 0, 8⟩]) (wr := [reg32 S 200, reg32 C 512])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · simp only [Proof.Sha3.permuteX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, d, dS.sub_left b8, dC.sub_left b8, dS.sub_left r4, dC.sub_left r4, fS, fC, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (below E (4 * [scr, st].length)) (by simp) 0 (by rw [eA]; simp) (by simp)
    · exact within (reg32 S 200) (by simp [wS]) 0 (by simp) (by simp)
    · exact within (reg32 C 640) (by simp [wC]) 0 (by simp) (by simp)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact within (reg32 S 200) (by simp [wS]) 0 (by simp) (by simp)
    · exact within (reg32 C 640) (by simp [wC]) 0 (by simp) (by simp)
  · rw [permute_stack, hesp] at f'
    have hsE : Frame [below E 12] s.mem (pushed [scr, st] s).callEntry.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    simp only [Proof.Sha3.permuteX86, arg_withRegions, State.withRegions_mem, a0, m₂] at post
    refine hQ s' rd' wr' cs' f' ?_
    rw [post]
    refine congrArg keccakF (Proof.Sha3.stateAt_congr fun i hi => ?_)
    exact hsE.bytes (R := reg32 S 200) (by simpa using dS.symm) (by simp) hi

end VG.Proof.Sha3.X86

end

/-!
# The SHA-3 sponge on x86 (32-bit): common lemmas

Facts about bytes, the stack and the variables `absorb` and `squeeze` keep in
their scratch space, which the proofs of the streaming functions share.
-/

namespace VG.Proof.Sha3.X86.Stream

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (addr_add_ofNat addr_toNat)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The low byte of a word in memory is its first byte. -/
theorem low_byte (m : Mem) (a : Addr) : (m.readW a 32).setWidth 8 = m a := by
  have := Mem.readW_byte m a (i := 0) (by omega)
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  rw [this]
  ext i hi
  simp

theorem xor_low (b : Byte) (w : BitVec 32) : (b.setWidth 32 ^^^ w).setWidth 8 = b ^^^ w.setWidth 8 := by
  ext i hi; simp

theorem byte_low (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

/-- The contract's stack region. -/
theorem stk_eq {E : BitVec 32} (h : 12 ≤ E.toNat) : below E 12 = ⟨E.setWidth 64 - 12, 12⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

/-- `[x + k]`, where nothing wraps around the 32-bit address space. -/
theorem ptr_addr {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) 0 = x.setWidth 64 + BitVec.ofNat 64 k := by
  rw [addr_add_ofNat (by omega), Nat.add_zero]

theorem ofNat_add_one (x : BitVec 32) (k : Nat) :
    x + BitVec.ofNat 32 k + 1 = x + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem add_sub_self (x y : BitVec 32) : x + y - x = y := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- A part of a region at a 32-bit pointer. -/
theorem sub_word {b : BitVec 32} {N d : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hd : d + 4 ≤ N) :
    Region.Sub ⟨addr b d, 4⟩ ⟨b.setWidth 64, N⟩ := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [addr_eq (by omega)] at hx
  have hE := addr_toNat b
  generalize b.setWidth 64 = B at *
  bv_omega

/-- Two words of a region at a 32-bit pointer that do not overlap. -/
theorem word_sep {b : BitVec 32} {N d e : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (hd : d + 4 ≤ N)
    (he : e + 4 ≤ N) (h : d + 4 ≤ e ∨ e + 4 ≤ d) (m : Mem) (v : BitVec 32) :
    (m.writeW (addr b e) v).readW (addr b d) 32 = m.readW (addr b d) 32 :=
  VG.Proof.Sha256.X86.Stream.readW_writeW_addr m v (by omega) (by omega) h

/-- A word of the argument area. -/
theorem arg_word {E : BitVec 32} {n d : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ n + 4) : Region.Sub ⟨addr E d, 4⟩ ⟨addr E 4, n⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha ⊢
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem arg_contains {E : BitVec 32} {n d : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ n + 4) : (⟨addr E 4, n⟩ : Region).Contains (addr E d) 4 := by
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega)]
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

/-- The arguments are above the return address, the stack the calls use below it. -/
theorem arg_stk {E : BitVec 32} {n : Nat} (hfit : E.toNat + 4 + n ≤ 2 ^ 32) (hlo : 12 ≤ E.toNat) :
    Region.Disjoint ⟨addr E 4, n⟩ (below E 12) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega)] at h₁
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem ret_stk {E : BitVec 32} (hfit : E.toNat + 4 ≤ 2 ^ 32) (hlo : 12 ≤ E.toNat) :
    Region.Disjoint ⟨E.setWidth 64, 4⟩ (below E 12) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE := addr_toNat E
  generalize E.setWidth 64 = b at *
  bv_omega

theorem argWord_eq {s : State} {n : Nat} (hsp : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {k : Nat}
    (hk : k < n) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.Sha3.X86.Stream

end
