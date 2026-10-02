import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Gcm.Ctr

/-!
# AES-GCM on x86: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `ecx` bytes
from `edi` to `edx`, and `xorLoop` XORs the `ecx` bytes at `edx` into those
at `edi`, a byte at a time, advancing both pointers (`copyLoop_ok`,
`xorLoop_ok`); the buffers do not overlap. Both are constant time from the
pointers and the count (`copyLoop_ct`, `xorLoop_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: the source `S` (`edi`), the
destination `D` (`edx`) and the count `n` (`ecx`). -/
structure LoopPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  edi : s.gpr .edi = S
  edx : s.gpr .edx = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fS : S.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem succ_ofNat32 (x : BitVec 32) (i : Nat) :
    x + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = x + BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem add_zero32 (x : BitVec 32) : x + BitVec.ofNat 32 0 = x := BitVec.add_zero x

theorem pred_count {n i : Nat} (h : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - (i + 1)) := by
  rw [ofNat_sub32 (by omega) (by omega)]; congr 1

theorem pred_beq {n i : Nat} (h : i < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = decide (i + 1 = n) := by
  rw [pred_count h hn, VG.X86.Wp.ofNat_beq_zero (by omega)]
  simp only [decide_eq_decide]
  omega

theorem setWidth8_32 (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  ext j hj; simp [hj]

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.movzx8 .eax (at_ .edi 0), .store8 (at_ .edx 0) .al, .alu .add .edi (imm 1),
    .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]

theorem copyStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .edi = S + BitVec.ofNat 32 i)
    (hd : s.gpr .edx = D + BitVec.ofNat 32 i) (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i))
    (eS : w64 (S + BitVec.ofNat 32 i) = w64 S + BitVec.ofNat 64 i)
    (eD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 D + BitVec.ofNat 64 i) (s.mem (w64 S + BitVec.ofNat 64 i)) ∧
      s'.gpr .edi = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .edx = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [copyBody, add_zero32, hs, hd, eS, eD, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, ite_true, setWidth8_32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, succ_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, succ_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · simp only [zf_setMem, gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 32) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

/-- What `copyLoop` leaves. -/
structure CopyPost (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n)
  edi : s'.gpr .edi = S + BitVec.ofNat 32 n
  edx : s'.gpr .edx = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copyLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s (CopyPost s S D n) := by
  have hn : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .edi = S + BitVec.ofNat 32 i ∧
      t.gpr .edx = D + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) i) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr)
    ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.edi, add_zero32], by rw [h.edx, add_zero32], by rw [h.ecx, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, edi, edx, ecx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', edi', edx', ecx', zf', g', rd', wr'⟩ := copyStep_ok t edi edx ecx
    (w64_add (by have := h.fS; omega)) (w64_add (by have := h.fD; omega))
    (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
    (by rw [wr]; exact in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem (w64 S) i).length = i := length_bytesAt _ _ _
  have hmem : t'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem (w64 D) (bytesAt s.mem (w64 S) i) _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by rw [zf', pred_beq hi hn]
  have gg : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edi', he], by rw [edx', he], gg,
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, edi', edx',
      by rw [ecx', pred_count hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.movzx8 .eax (at_ .edx 0), .movzx8 .ebx (at_ .edi 0), .alu .xor .eax (.reg .ebx),
    .store8 (at_ .edi 0) .al, .alu .add .edi (imm 1), .alu .add .edx (imm 1), .alu .sub .ecx (imm 1)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : BitVec 32)).setWidth 8 = a ^^^ b := by
  ext j hj; simp [hj]

theorem xorStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .edx = S + BitVec.ofNat 32 i)
    (hd : s.gpr .edi = D + BitVec.ofNat 32 i) (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i))
    (eS : w64 (S + BitVec.ofNat 32 i) = w64 S + BitVec.ofNat 64 i)
    (eD : w64 (D + BitVec.ofNat 32 i) = w64 D + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 D + BitVec.ofNat 64 i) 1)
    (w' : InRegions (s.rd ++ s.wr) (w64 D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa xorBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 D + BitVec.ofNat 64 i)
        (s.mem (w64 S + BitVec.ofNat 64 i) ^^^ s.mem (w64 D + BitVec.ofNat 64 i)) ∧
      s'.gpr .edx = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .edi = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by xrun [xorBody, add_zero32, hs, hd, eS, eD, r, w, w'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, Reg8.reg, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, setWidth8_xor]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, succ_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, succ_ofNat32]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · simp only [zf_setMem, gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hc]
  · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄, h₅]
  all_goals rfl

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    xorBytes m D S (i + 1) = xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [xorBytes, bytesAt_succ, List.zipWith_append, length_bytesAt]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (xorBytes m D S n).length = n := by
  simp [xorBytes, length_bytesAt]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

/-- What `xorLoop` (source `S` in `edx`, destination `D` in `edi`) leaves. -/
structure XorPost (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 D) (w64 S) n)
  edx : s'.gpr .edx = S + BitVec.ofNat 32 n
  edi : s'.gpr .edi = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- What `xorLoop` needs: the source `S` in `edx`, the destination `D` in `edi`. -/
structure XorPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  edx : s.gpr .edx = S
  edi : s.gpr .edi = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fS : S.toNat + n ≤ 2 ^ 32
  fD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem xorLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : XorPre s S D n) :
    WP isa xorLoop s (XorPost s S D n) := by
  have hn : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .edx = S + BitVec.ofNat 32 i ∧
      t.gpr .edi = D + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 D) (w64 S) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.edx, add_zero32], by rw [h.edi, add_zero32], by rw [h.ecx, Nat.sub_zero],
      by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, edx, edi, ecx, mem, g, rd, wr⟩
  have wD : InRegions t.wr (w64 D + BitVec.ofNat 64 i) 1 := by rw [wr]; exact in_of_covers h.wr hi (by omega)
  obtain ⟨t', run', mem', edx', edi', ecx', zf', g', rd', wr'⟩ := xorStep_ok t edx edi ecx
    (w64_add (by have := h.fS; omega)) (w64_add (by have := h.fD; omega))
    (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega)) wD (in_left wD)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_xorBytes s.mem (w64 D) (w64 S) i
  have hmem : t'.mem = writeBytes s.mem (w64 D) (xorBytes s.mem (w64 D) (w64 S) (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi hn _ hlen, dst_kept hi hn _ hlen, xorBytes_succ, BitVec.xor_comm,
      writeBytes_snoc s.mem (w64 D) _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by rw [zf', pred_beq hi hn]
  have gg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edi → r ≠ .edx → r ≠ .ecx → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edx', he], by rw [edi', he], gg,
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, edx', edi',
      by rw [ecx', pred_count hi hn], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## Constant time -/

theorem copyLoop_ct {I : State → Prop} (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r) :
    CT I copyLoop :=
  CT.taint _ hr (by taint_decide)

theorem xorLoop_ct {I : State → Prop} (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.edi, .edx, .ecx], s₁.gpr r = s₂.gpr r) :
    CT I xorLoop :=
  CT.taint _ hr (by taint_decide)

end VG.Proof.AesGcm.X86
