import VerifiedGarbage.Proof.AesGcm.Arm.Run

/-!
# AES-GCM on ARMv7: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `r3` bytes
from `r1` to `r2`, and `xorLoop` XORs `r3` bytes at `r1` into those at `r2`,
a byte at a time through advancing pointers, counting `r3` down to zero
(`copyLoop_ok`, `xorLoop_ok`); the buffers do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: `n` (at least 1) bytes at the 32-bit
pointers `S` (read) and `D` (written). -/
structure LoopPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  r1 : s.gpr .r1 = S
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fitS : S.toNat + n ≤ 2 ^ 32
  fitD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨State.addr D, n⟩] s.wr
  disj : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr D, n⟩

/-- What the loops leave, but memory. -/
structure LoopOut (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  r1 : s'.gpr .r1 = S + BitVec.ofNat 32 n
  r2 : s'.gpr .r2 = D + BitVec.ofNat 32 n
  r3 : s'.gpr .r3 = 0
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem addr_i {P : BitVec 32} {n i : Nat} (hf : P.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    State.addr (P + BitVec.ofNat 32 i) = State.addr P + BitVec.ofNat 64 i := addr_add (by omega)

theorem setWidth8_32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem dec32 {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - (i + 1)) := by
  rw [ofNat_sub32 (by omega) (by omega)]; congr 1

theorem z_dec {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - (i + 1)) == 0) = decide (i + 1 = n) := by
  rw [z_cmp0 (by omega)]; congr 1; apply propext; omega

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.ldrb .r12 .r1 0, .strb .r12 .r2 0, addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]

theorem copyStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 i)
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 i) (hn : s.gpr .r3 = BitVec.ofNat 32 (n - i))
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i)) (s.mem (State.addr (S + BitVec.ofNat 32 i))) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨_, by arun [hs, hd, hn, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, setWidth8_32]
  · simp [gpr_setReg, hs, add32_ofNat_assoc]
  · simp [gpr_setReg, hd, add32_ofNat_assoc]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

theorem copyLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) n) ∧
      LoopOut s S D n s' := by
  have hn32 : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r1 = S + BitVec.ofNat 32 i ∧
      t.gpr .r2 = D + BitVec.ofNat 32 i ∧ t.gpr .r3 = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1, add_ofNat_zero], by rw [h.r2, add_ofNat_zero], by rw [h.r3]; rfl,
      by simp [bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r1, r2, r3, mem, g, rd, wr, sp⟩
  have aS := addr_i h.fitS hi
  have aD := addr_i h.fitD hi
  obtain ⟨t', run', mem', r1', r2', r3', z', g', rd', wr', sp'⟩ := copyStep_ok t r1 r2 r3
    (by rw [rd, wr, aS]; exact in_of_covers h.rd hi (by omega))
    (by rw [wr, aD]; exact in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem (State.addr S) i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (i + 1)) := by
    rw [mem', mem, aS, aD, src_kept h.disj hi (by omega) _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem _ (bytesAt s.mem _ i) _ (by rw [hlen]; omega), hlen]
  have hz : t'.z = decide (i + 1 = n) := by rw [z', dec32 hi hn32, z_dec hi hn32]
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  have ev : isa.eval .ne t' = some !decide (i + 1 = n) := eval_ne' hz
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r1', he], by rw [r2', he], ?_,
      fun r h₀ h₁ h₂ h₃ h₄ => gg r h₁ h₂ h₃ h₄, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r3', dec32 hi hn32, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r1', r2',
      by rw [r3', dec32 hi hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.ldrb .r12 .r2 0, .ldrb .r0 .r1 0, .dp .eor .r12 .r12 (.reg .r0), .strb .r12 .r2 0,
    addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : BitVec 32)).setWidth 8 = a ^^^ b := by
  ext j hj; simp

theorem xorStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 i)
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 i) (hn : s.gpr .r3 = BitVec.ofNat 32 (n - i))
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa xorBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        (s.mem (State.addr (D + BitVec.ofNat 32 i)) ^^^ s.mem (State.addr (S + BitVec.ofNat 32 i))) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have w' : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1 := in_left w
  refine ⟨_, by arun [hs, hd, hn, add_ofNat_zero, r, w, w'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, setWidth8_xor]
  · simp [gpr_setReg, hs, add32_ofNat_assoc]
  · simp [gpr_setReg, hd, add32_ofNat_assoc]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · intro r h₀ h₁ h₂ h₃ h₄; simp [gpr_setReg, h₀, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    xorBytes m D S (i + 1) = xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [xorBytes, bytesAt_succ, List.zipWith_append, Cmac.bytesAt_length]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (xorBytes m D S n).length = n := by
  simp [xorBytes, Cmac.bytesAt_length]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 63) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

theorem xorLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : LoopPre s S D n) :
    WP isa xorLoop s fun s' =>
      s'.mem = writeBytes s.mem (State.addr D) (xorBytes s.mem (State.addr D) (State.addr S) n) ∧
      LoopOut s S D n s' := by
  have hn32 : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r1 = S + BitVec.ofNat 32 i ∧
      t.gpr .r2 = D + BitVec.ofNat 32 i ∧ t.gpr .r3 = BitVec.ofNat 32 (n - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (xorBytes s.mem (State.addr D) (State.addr S) i) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1, add_ofNat_zero], by rw [h.r2, add_ofNat_zero], by rw [h.r3]; rfl,
      by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r1, r2, r3, mem, g, rd, wr, sp⟩
  have aS := addr_i h.fitS hi
  have aD := addr_i h.fitD hi
  obtain ⟨t', run', mem', r1', r2', r3', z', g', rd', wr', sp'⟩ := xorStep_ok t r1 r2 r3
    (by rw [rd, wr, aS]; exact in_of_covers h.rd hi (by omega))
    (by rw [wr, aD]; exact in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_xorBytes s.mem (State.addr D) (State.addr S) i
  have hmem : t'.mem = writeBytes s.mem (State.addr D) (xorBytes s.mem (State.addr D) (State.addr S) (i + 1)) := by
    rw [mem', mem, aS, aD, src_kept h.disj hi (by omega) _ hlen, dst_kept hi (by omega) _ hlen, xorBytes_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.z = decide (i + 1 = n) := by rw [z', dec32 hi hn32, z_dec hi hn32]
  have gg : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ => by rw [g' r h₀ h₁ h₂ h₃ h₄, g r h₀ h₁ h₂ h₃ h₄]
  have ev : isa.eval .ne t' = some !decide (i + 1 = n) := eval_ne' hz
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r1', he], by rw [r2', he], ?_, gg,
      by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r3', dec32 hi hn32, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r1', r2',
      by rw [r3', dec32 hi hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

end VG.Proof.AesGcm.Arm
