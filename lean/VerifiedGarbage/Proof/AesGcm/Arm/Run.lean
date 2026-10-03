import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-GCM on ARMv7: running straight-line blocks

Untrusted: everything here is checked by Lean. `arun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`), and
the memory facts shared by the pieces: what `DataOk` says of a buffer of
data, and the bytes written by a copy (`bytesAt_writeBytes`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)

@[simp] theorem gpr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
@[simp] theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
@[simp] theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
@[simp] theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
@[simp] theorem sp_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
@[simp] theorem z_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl
@[simp] theorem c_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl
/-- `s` with the memory `m`: what a store leaves, kept folded in symbolic
execution (unfolded, the structure update would copy the state into each
of its fields). -/
def withMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (withMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (withMem s (s.mem.writeW a x)) else none := rfl
@[simp] theorem sp_store (s : State) (m : Mem) : (withMem s m).sp = s.sp := rfl
@[simp] theorem gpr_store (s : State) (m : Mem) : (withMem s m).gpr = s.gpr := rfl
@[simp] theorem rd_store (s : State) (m : Mem) : (withMem s m).rd = s.rd := rfl
@[simp] theorem wr_store (s : State) (m : Mem) : (withMem s m).wr = s.wr := rfl
@[simp] theorem mem_store (s : State) (m : Mem) : (withMem s m).mem = m := rfl
@[simp] theorem z_store (s : State) (m : Mem) : (withMem s m).z = s.z := rfl
@[simp] theorem c_store (s : State) (m : Mem) : (withMem s m).c = s.c := rfl

theorem op2_imm' {s : State} {n : Nat} (h : encodable (BitVec.ofNat 32 n) = true) :
    (imm n).eval s = some (BitVec.ofNat 32 n) := by simp only [imm, Op2.eval, h, ite_true]

/-- An immediate's encodability, decided by `arun`'s discharger. -/
theorem encodable_of_decide {v : BitVec 32} (h : encodable v = true) : encodable v = true := h

/-- Runs a block of the instructions the AES-GCM code uses. -/
macro "arun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, imm, addI, State.load32, store32_eq, State.load8, store8_eq,
    tO, uO, vO, rO, scrO, List.cons_append, List.nil_append, List.append_assoc, Option.map_some,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg, c_setReg, gpr_subFlags, mem_subFlags,
    rd_subFlags, wr_subFlags, sp_subFlags, z_subFlags, c_subFlags, sp_store, gpr_store, rd_store, wr_store,
    mem_store, z_store, c_store, ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, and_self, and_true, true_and, encodable_of_decide,
    eq_self_iff_true, $ts,*]) <;>
  try rfl)

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from the state, `W` and the stack below `sp`. -/
structure DataOk (st w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  lt32 : n < 2 ^ 32
  fit : D.toNat + n ≤ 2 ^ 32
  st : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr st, 80⟩
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (below sp).Disjoint ⟨State.addr D, n⟩

namespace DataOk

variable {st w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : DataOk st w sp s D n)
include h

theorem lt : n < 2 ^ 64 := by have := h.fit; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataOk st w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : DataOk st w sp s D k where
  rd := covers_prefix h.rd hk
  lt32 := by have := h.lt32; omega
  fit := by have := h.fit; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : DataOk st w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, by have := h.lt32; omega, ?_, ?_, ?_, ?_⟩
  · rw [ha]; exact covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega)]; have := h.fit; omega
  · rw [ha]; exact h.st.sub_left hs
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end DataOk

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes at `p`, after writing `xs` at `p + o`: the first `o`, then `xs`. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (o : Nat) (xs : List Byte) (h : o + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p (o + xs.length) = bytesAt m p o ++ xs := by
  rw [bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₁, ite_true,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  have := bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, bytesAt_add, bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬ (xs.length + i < xs.length) by omega]

/-- Running a block with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

theorem eval_eq' {s : State} {b : Bool} (h : s.z = b) : isa.eval .eq s = some b := by
  show VG.Arm.eval .eq s = _; rw [VG.Proof.MdStream.Arm.eval_eq, h]

theorem eval_ne' {s : State} {b : Bool} (h : s.z = b) : isa.eval .ne s = some !b := by
  show VG.Arm.eval .ne s = _; rw [VG.Proof.MdStream.Arm.eval_ne, h]

/-- `Z` after `cmp` of a register holding `n` with `k`. -/
theorem z_cmp {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := VG.Proof.MdStream.Arm.sub_beq ha hb

theorem z_cmp0 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a == 0) = decide (a = 0) :=
  VG.Proof.MdStream.Arm.ofNat_beq_zero ha

theorem ofNat_sub32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem ofNat_add32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem toNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := toNat_ofNat32 h

theorem and15 (x : BitVec 32) : x &&& BitVec.ofNat 32 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 4 = BitVec.ofNat 32 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.AesGcm.Arm
