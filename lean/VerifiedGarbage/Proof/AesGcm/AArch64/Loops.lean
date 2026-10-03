import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Cmac.Block

/-!
# AES-GCM on AArch64: the byte loops and `minK`

Untrusted: everything here is checked by Lean. `copy` copies `x13` bytes
from `x12` to `x11`, and `xor` XORs `x13` bytes at `x11` into those at `x12`,
a byte at a time through advancing pointers (`copy_ok`, `xor_ok`); the buffers
do not overlap. `minK` computes `min (16 - x25, x24)` (`minK_ok`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem byte_rt (b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  have := Mem.extractLsb'_read m a (n := 1) (j := 0) (by decide)
  rw [show 8 * 0 = 0 from rfl, BitVec.extractLsb'_eq_self, show BitVec.ofNat 64 0 = 0#64 from rfl,
    BitVec.add_zero] at this
  exact this

theorem succ_ofNat (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: `n` bytes at `S` (read) and at `D`
(written), apart. -/
structure LoopPre (s : State) (S D : Addr) (n : Nat) : Prop where
  lt : n < 2 ^ 63
  rd : Covers [⟨S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, n⟩] s.wr
  disj : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩

/-- The registers the loops write. -/
abbrev loopRegs : List Reg := [.x11, .x12, .x13, .x14, .x15]

/-! ## `copy` -/

abbrev copyBody : List Instr :=
  [.ldrb .x14 .x12 0, .strb .x14 .x11 0, .addImm .x .x12 .x12 1, .addImm .x .x11 .x11 1,
    .subImm .x .x13 .x13 1]

theorem copyStep_ok (s : State) {A B : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x11 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) A 1) (w : InRegions s.wr B 1) :
    ∃ s', runBlock isa copyBody s = some s' ∧ s'.mem = s.mem.writeW B (s.mem A) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x11 = s.gpr .x11 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      (∀ r, r ∉ loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, byte_rt, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄, -⟩ := h
    simp [gpr_write, h₁, h₂, h₃, h₄]

theorem copyLoop_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x12 = S) (hD : s.gpr .x11 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (hpos : 0 < n) (h : LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      s'.gpr .x12 = S + BitVec.ofNat 64 n ∧ s'.gpr .x11 = D + BitVec.ofNat 64 n ∧
      (∀ r, r ∉ loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.loop (M := isa) (body := .block copyBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = S + BitVec.ofNat 64 i ∧
      t.gpr .x11 = D + BitVec.ofNat 64 i ∧ t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hpos, by rw [hS]; simp, by rw [hD]; simp, by rw [hn, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x11, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x11', x13', g', sp', rd', wr'⟩ := copyStep_ok t
    (A := S + BitVec.ofNat 64 i) (B := D + BitVec.ofNat 64 i) (by rw [x12, BitVec.add_zero])
    (by rw [x11, BitVec.add_zero]) (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
    (by rw [wr]; exact in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem S i).length = i := length_bytesAt _ _ _
  have hx : writeBytes s.mem D (bytesAt s.mem S i) (S + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem D _ (R := ⟨D, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact h.disj _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
    rw [mem', mem, hx, bytesAt_succ,
      writeBytes_snoc s.mem D (bytesAt s.mem S i) (s.mem (S + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : ∀ r, r ∉ loopRegs → t'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x12', x12, BitVec.add_assoc, succ_ofNat, he],
      by rw [x11', x11, BitVec.add_assoc, succ_ofNat, he], gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, succ_ofNat], by rw [x11', x11, BitVec.add_assoc, succ_ofNat],
      x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-- `copy`: the `n` bytes at `S` to `D`. -/
theorem copy_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x12 = S) (hD : s.gpr .x11 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (h : LoopPre s S D n) :
    WP isa copy s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ∉ loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.ite (decide (n = 0)) (eval_zero hn (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    exact WP.mono (copyLoop_ok s hS hD hn (by omega) h) fun s' ⟨m, _, _, g, sp, rd, wr⟩ => ⟨m, g, sp, rd, wr⟩

/-! ## `xor` -/

abbrev xorBody : List Instr :=
  [.ldrb .x14 .x12 0, .ldrb .x15 .x11 0, .logic .eor .w .x14 .x14 .x15, .strb .x14 .x12 0,
    .addImm .x .x12 .x12 1, .addImm .x .x11 .x11 1, .subImm .x .x13 .x13 1]

theorem byte_xor (a b : BitVec (8 * 1)) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) ^^^
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))))) = a ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, show i < 64 by omega, show i < 32 by omega,
    hi, decide_true, Bool.true_and]

theorem xorStep_ok (s : State) {A B : Addr} (ha : s.gpr .x12 + BitVec.ofNat 64 0 = A)
    (hb : s.gpr .x11 + BitVec.ofNat 64 0 = B)
    (r : InRegions (s.rd ++ s.wr) B 1) (w : InRegions s.wr A 1) :
    ∃ s', runBlock isa xorBody s = some s' ∧ s'.mem = s.mem.writeW A (s.mem A ^^^ s.mem B) ∧
      s'.gpr .x12 = s.gpr .x12 + 1 ∧ s'.gpr .x11 = s.gpr .x11 + 1 ∧ s'.gpr .x13 = s.gpr .x13 - 1 ∧
      (∀ r, r ∉ loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have wa := in_left (rd := s.rd) w
  refine ⟨_, by
    simp (config := {decide := true}) only [xorBody, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, hb, r, w, wa]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h => ?_, rfl, rfl, rfl⟩
  · simp only [mem_write, Mem.writeW, byte_xor, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]
  · simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅]

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    xorBytes m D S (i + 1) = xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [xorBytes, bytesAt_succ, List.zipWith_append, length_bytesAt]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (xorBytes m D S n).length = n := by
  simp [xorBytes, length_bytesAt]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 63) (xs : List Byte)
    (hxs : xs.length = i) : writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

/-- The source byte `i` is not overwritten so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

/-- `xorLoop`: the `n` bytes at `S` (`x11`) XORed into those at `D` (`x12`). -/
theorem xorLoop_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x11 = S) (hD : s.gpr .x12 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (hpos : 0 < n) (h : LoopPre s S D n) :
    WP isa xorLoop s fun s' => s'.mem = writeBytes s.mem D (xorBytes s.mem D S n) ∧
      (∀ r, r ∉ loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.loop (M := isa) (body := .block xorBody) (c := .nonzero .x .x13)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .x12 = D + BitVec.ofNat 64 i ∧
      t.gpr .x11 = S + BitVec.ofNat 64 i ∧ t.gpr .x13 = BitVec.ofNat 64 (n - i) ∧
      t.mem = writeBytes s.mem D (xorBytes s.mem D S i) ∧
      (∀ r, r ∉ loopRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hpos, by rw [hD]; simp, by rw [hS]; simp, by rw [hn, Nat.sub_zero],
      by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, x12, x11, x13, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x12', x11', x13', g', sp', rd', wr'⟩ := xorStep_ok t
    (A := D + BitVec.ofNat 64 i) (B := S + BitVec.ofNat 64 i) (by rw [x12, BitVec.add_zero])
    (by rw [x11, BitVec.add_zero]) (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
    (by rw [wr]; exact in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := length_xorBytes s.mem D S i
  have hmem : t'.mem = writeBytes s.mem D (xorBytes s.mem D S (i + 1)) := by
    rw [mem', mem, src_kept h.disj hi h.lt _ hlen, dst_kept hi h.lt _ hlen, xorBytes_succ,
      writeBytes_snoc s.mem D _ _ (by rw [hlen]; omega), hlen]
  have x13'' : t'.gpr .x13 = BitVec.ofNat 64 (n - (i + 1)) := by
    rw [x13', x13, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (r := .x13) (a := n - (i + 1)) x13'' (by omega)
  have gg : ∀ r, r ∉ loopRegs → t'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [ev]; simp; omega, n - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x12', x12, BitVec.add_assoc, succ_ofNat], by rw [x11', x11, BitVec.add_assoc, succ_ofNat],
      x13'', hmem, gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

/-- `xor`: the `n` bytes at `S` (`x11`) XORed into those at `D` (`x12`). -/
theorem xor_ok (s : State) {S D : Addr} {n : Nat} (hS : s.gpr .x11 = S) (hD : s.gpr .x12 = D)
    (hn : s.gpr .x13 = BitVec.ofNat 64 n) (h : LoopPre s S D n) :
    WP isa xor s fun s' => s'.mem = writeBytes s.mem D (xorBytes s.mem D S n) ∧
      (∀ r, r ∉ loopRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine WP.ite (decide (n = 0)) (eval_zero hn (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by simp [xorBytes, bytesAt, writeBytes_nil], fun _ _ => rfl, rfl, rfl, rfl⟩
  · have h0 : n ≠ 0 := by simpa using hf
    exact xorLoop_ok s hS hD hn (by omega) h

/-! ## `minK` -/

/-- The registers `minK` writes. -/
abbrev minRegs : List Reg := [.x9, .x10, .x11]

theorem minK_ok (s : State) {o n : Nat} (h25 : s.gpr .x25 = BitVec.ofNat 64 o)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 n) (ho : o < 16) (hn : n < 2 ^ 64) :
    WP isa minK s fun s' => s'.gpr .x10 = BitVec.ofNat 64 (min (16 - o) n) ∧
      (∀ r, r ∉ minRegs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x9₁, x10₁, g₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [imm .x9 16, .sub .x .x9 .x9 .x25, .lsr .x .x10 .x24 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 (16 - o) ∧ s₁.gpr .x10 = BitVec.ofNat 64 (n / 16) ∧
      (∀ r, r ∉ minRegs → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, h25, ofNat_sub (show o ≤ 16 by omega) (show 16 < 2 ^ 64 by decide)]
    · simp [gpr_write, h24, lsr_ofNat _ _ hn]
    · simp only [minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.1, hr.2.1]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (!decide (n / 16 = 0)) (eval_nonzero x10₁ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h16 : 16 ≤ n := by simp at ht; omega
    refine WP.run (Q := fun s' => s' = s₁.write .x .x10 (s₁.gpr .x9 + BitVec.ofNat 64 0)) ⟨_, by arun [], rfl⟩
      fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r hr => ?_, m₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, ite_true, x9₁, BitVec.add_zero, BitVec.setWidth_eq]
      rw [Nat.min_eq_left (by omega)]
    · simp only [minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, hr.2.1, ite_false]; exact g₁ r (by simp [minRegs, hr.1, hr.2.1, hr.2.2])
  · have h16 : n < 16 := by simp at hf; omega
    obtain ⟨s₂, run₂, x11₂, g₂, m₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
        [.sub .x .x11 .x9 .x24, .lsr .x .x11 .x11 63] s₁ = some s₂ ∧
        s₂.gpr .x11 = BitVec.ofNat 64 (if n ≤ 16 - o then 0 else 1) ∧
        (∀ r, r ≠ .x11 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧
        s₂.wr = s₁.wr := by
      refine ⟨_, by arun [], ?_⟩
      refine ⟨?_, fun r hr => by simp [gpr_write, hr], rfl, rfl, rfl, rfl⟩
      simp only [gpr_write, ite_true, x9₁, g₁ .x24 (by decide), h24, BitVec.setWidth_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega),
        toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]
      by_cases hc : n ≤ 16 - o
      · simp only [hc, ↓reduceIte]
        rw [toNat_ofNat_of_lt (by decide), Nat.div_eq_of_lt (by omega)]
      · simp only [hc, ↓reduceIte]
        rw [toNat_ofNat_of_lt (by decide)]
        omega
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hg : ∀ r, r ∉ minRegs → s₂.gpr r = s.gpr r := fun r hr => by
      rw [g₂ r (by simp only [minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2),
        g₁ r hr]
    by_cases hc : n ≤ 16 - o
    · simp only [hc, ↓reduceIte] at x11₂
      refine WP.ite true (by rw [eval_zero x11₂ (by decide)]; rfl) (fun _ => ?_) (fun h => by cases h)
      refine WP.run (Q := fun s' => s' = s₂.write .x .x10 (s₂.gpr .x24 + BitVec.ofNat 64 0))
        ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
      subst hs'
      refine ⟨?_, fun r hr => ?_, by rw [mem_write, m₂, m₁], by rw [sp_write, sp₂, sp₁],
        by rw [rd_write, rd₂, rd₁], by rw [wr_write, wr₂, wr₁]⟩
      · simp only [gpr_write, ite_true, BitVec.add_zero, BitVec.setWidth_eq, g₂ .x24 (by decide),
          g₁ .x24 (by decide), h24]
        rw [Nat.min_eq_right hc]
      · simp only [minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [gpr_write, hr.2.1, ite_false]; exact hg r (by simp [minRegs, hr.1, hr.2.1, hr.2.2])
    · simp only [hc, ↓reduceIte] at x11₂
      refine WP.ite false (by rw [eval_zero x11₂ (by decide)]; rfl) (fun h => by cases h) (fun _ => ?_)
      refine WP.run (Q := fun s' => s' = s₂.write .x .x10 (s₂.gpr .x9 + BitVec.ofNat 64 0))
        ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
      subst hs'
      refine ⟨?_, fun r hr => ?_, by rw [mem_write, m₂, m₁], by rw [sp_write, sp₂, sp₁],
        by rw [rd_write, rd₂, rd₁], by rw [wr_write, wr₂, wr₁]⟩
      · simp only [gpr_write, ite_true, BitVec.add_zero, BitVec.setWidth_eq, g₂ .x9 (by decide), x9₁]
        rw [Nat.min_eq_left (by omega)]
      · simp only [minRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [gpr_write, hr.2.1, ite_false]; exact hg r (by simp [minRegs, hr.1, hr.2.1, hr.2.2])

/-! ## Bytes written -/

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
  simp [show ¬xs.length + i < xs.length by omega]

/-- The bytes of `bytesAt m D n` from `j` on. -/
theorem bytesAt_drop (m : Mem) (D : Addr) {j n : Nat} (hj : j ≤ n) :
    (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := by
  rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
    Nat.add_sub_cancel_left]

/-- The first `k` bytes of `bytesAt m D n`. -/
theorem bytesAt_take (m : Mem) (D : Addr) {k n : Nat} (hk : k ≤ n) :
    (bytesAt m D n).take k = bytesAt m D k := by
  rw [show n = k + (n - k) by omega, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

end VG.Proof.AesGcm.AArch64
