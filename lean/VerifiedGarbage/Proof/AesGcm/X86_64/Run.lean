import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM on x86-64: running straight-line blocks

Untrusted: everything here is checked by Lean. `xrun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`), and
the memory facts shared by the pieces: what `DataOk` says of a buffer of
data, and the bytes written by a copy (`bytesAt_writeBytes`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- Runs a block of the instructions the AES-GCM code uses. -/
macro "xrun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, stO, tO, uO, roundsO, alenO, tlenO, dataO,
    lenO, auxO, tlO, aadO, vO, rO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, and_self, and_true, true_and, $ts,*]) <;> try rfl)

/-- A buffer of `n` bytes at `D` that the code may read, apart from the
context, the state, `W` and the stack below `SP`. -/
structure DataOk (St W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  st : (⟨D, n⟩ : Region).Disjoint ⟨St, 80⟩
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 8).Disjoint ⟨D, n⟩

namespace DataOk

variable {St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DataOk St W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataOk St W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : DataOk St W SP s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega
  st := h.st.sub_left (Offset.sub_base D (by omega))
  w := h.w.sub_left (Offset.sub_base D (by omega))
  stk := h.stk.sub_right (Offset.sub_base D (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : DataOk St W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

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

end VG.Proof.AesGcm.X86_64
