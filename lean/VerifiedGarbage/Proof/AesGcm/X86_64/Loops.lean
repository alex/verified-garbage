import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM on x86-64: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `rcx`
bytes from `rsi` to `rdi`, and `xorLoop` XORs `rcx` bytes at `rsi` into those
at `rdi`, a byte at a time with the index in `r10` (`copyLoop_ok`,
`xorLoop_ok`); the buffers do not overlap.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem ea_idx (s : State) (b : Reg) {B : Addr} (hb : s.gpr b = B) {i : Nat}
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) :
    s.gpr b + s.gpr .r10 * BitVec.ofNat 64 1 + BitVec.ofInt 64 (0 : Int) = B + BitVec.ofNat 64 i := by
  rw [hb, hi, BitVec.mul_one]; simp

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state. -/
structure LoopPre (s : State) (S D : Addr) (n : Nat) : Prop where
  rsi : s.gpr .rsi = S
  rdi : s.gpr .rdi = D
  rcx : s.gpr .rcx = BitVec.ofNat 64 n
  pos : 1 ≤ n
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.movzx8 .rax srcB, .store8 dstB .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

theorem copyStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i) (s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, srcB, dstB, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, ite_true, ite_false,
      e₁, e₂, r, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

theorem copyLoop_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok t
    (by rw [g _ (by decide) (by decide), h.rsi]) (by rw [g _ (by decide) (by decide), h.rdi]) r10
    (by rw [g _ (by decide) (by decide), h.rcx])
    (by rw [rd, wr]; exact in_of_covers h.rd hi (by have := h.lt; omega))
    (by rw [wr]; exact in_of_covers h.wr hi (by have := h.lt; omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := by simp [bytesAt]
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi h.lt _ hlen, bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; have := h.lt; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega) (by have := h.lt; omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → t'.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.movzx8 .rax dstB, .movzx8 .r11 srcB, .alu .xor .rax (.reg .r11), .store8 dstB .rax,
    .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 64 ^^^ b.setWidth 64 : BitVec 64)).setWidth 8 = a ^^^ b := by
  ext j hj; simp

theorem xorStep_ok (s : State) {S D : Addr} {i n : Nat} (hs : s.gpr .rsi = S) (hd : s.gpr .rdi = D)
    (hi : s.gpr .r10 = BitVec.ofNat 64 i) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (r : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (D + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa xorBody s = some s' ∧
      s'.mem = s.mem.writeW (D + BitVec.ofNat 64 i)
        (s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (S + BitVec.ofNat 64 i)) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + 1 ∧
      s'.zf = some (BitVec.ofNat 64 i + 1 - BitVec.ofNat 64 n == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  have wr' : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨x, hx, hc⟩ := w; exact ⟨x, List.mem_append_right _ hx, hc⟩
  refine ⟨_, by
    simp (config := {decide := true}) only [xorBody, srcB, dstB, imm, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some,
      Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags,
      wr_setReg, wr_arithFlags, ite_true, ite_false, e₁, e₂, r, w, wr']
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, setWidth8_xor]
  · simp [gpr_setReg, hi]
  · simp [hi, hn]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]

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

theorem xorLoop_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa xorLoop s fun s' => s'.mem = writeBytes s.mem D (xorBytes s.mem D S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, r10₁, g₁⟩ : ∃ s₁, runBlock isa [.mov32 .r10 (imm 0)] s = some s₁ ∧
      s₁.gpr .r10 = BitVec.ofNat 64 0 ∧ s₁ = s.setReg .r10 (BitVec.setWidth 64 (BitVec.ofNat 32 0)) :=
    ⟨_, by simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      State.setReg32], by simp [gpr_setReg], rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  subst g₁
  refine WP.loop (M := isa) (body := .block xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r10 = BitVec.ofNat 64 i ∧
      t.mem = writeBytes s.mem D (xorBytes s.mem D S i) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, h.pos, r10₁, by simp [xorBytes, bytesAt, writeBytes_nil, mem_setReg],
      fun r h₁ h₂ _ => by simp [gpr_setReg, h₂], rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', r10', zf', g', rd', wr'⟩ := xorStep_ok t
    (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
    (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10
    (by rw [g _ (by decide) (by decide) (by decide), h.rcx])
    (by rw [rd, wr]; exact in_of_covers h.rd hi (by have := h.lt; omega))
    (by rw [wr]; exact in_of_covers h.wr hi (by have := h.lt; omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_xorBytes s.mem D S i
  have hmem : t'.mem = writeBytes s.mem D (xorBytes s.mem D S (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi h.lt _ hlen, dst_kept hi h.lt _ hlen, xorBytes_succ,
      writeBytes_snoc s.mem D _ _ (by rw [hlen]; have := h.lt; omega), hlen]
  have hz : t'.zf = some (decide (i + 1 = n)) := by
    rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega) (by have := h.lt; omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r11 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ => by rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : i + 1 = n
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
      hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesGcm.X86_64
