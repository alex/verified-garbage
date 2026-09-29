import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset

/-!
# HMAC over any streaming hash function on x86-64: the byte loops

Untrusted: everything here is checked by Lean. The byte copy (`copy`), used
for states, digests and `U`; the exclusive-or of `U` into `T`; and `init`'s
loops that write `K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each counts `r14` up from 0
and ends when it reaches its bound.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash byteAt copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeW8_apply)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov32i wp_addi wp_cmp wp_cmpi wp_movzx8 wp_store8
  ofNat_succ sub_beq)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' xorBytes_snoc xorBytes_length'
  add_ofNat_add not_mem_of_disjoint InRegions.right' BufMem buf_write K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)

/-! ## Arithmetic -/

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega)]
  exact zx_ofNat (by omega)

theorem sx_one : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem ea_byteAt (s : State) (b : Reg) (o k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea (byteAt b o) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  simp only [State.ea, byteAt, h14, ofInt_natCast, show BitVec.ofNat 64 1 = 1 from rfl]
  ac_rfl

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by simp [eval, hz, hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [eval, hz, hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-- `r14` counted up to `n`: the flags after `add r14, 1; cmp r14, n`. -/
theorem count_zf {k n : Nat} (hk : k < n) (hn : n < 2 ^ 31) :
    (BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 - (BitVec.ofNat 32 n).signExtend 64 == 0) =
      decide (k + 1 = n) := by
  rw [sx_one, sx_ofNat hn, ← ofNat_succ, sub_beq (by omega) (by omega)]

/-! ## `copy` -/

/-- After `k` bytes of `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ≠ .rax ∧ src ≠ .r14) (hd : dst ≠ .rax ∧ dst ≠ .r14)
    {so d n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State}
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr src + BitVec.ofNat 64 so, n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      Copied s (s.gpr dst + BitVec.ofNat 64 d) (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 so) n) t := by
  set A := s.gpr src + BitVec.ofNat 64 so
  set B := s.gpr dst + BitVec.ofNat 64 d
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (count_loop hn (CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k) (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ hs.1 hs.2])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ hd.1,
      h.other _ hd.1 hd.2]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmpi fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14, sx_one, ← ofNat_succ], ?_⟩, by rw [z₄, h14, count_zf hk hn']⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, bytesAt_snoc']
  have e : writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
  have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega)
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']

/-! ## The exclusive-or of `U` into `T` -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ (s.gpr r).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ v).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.imm v) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem xor_byte2 (a b : Byte) :
    ((((a.setWidth 64).setWidth 32 ^^^ (b.setWidth 64).setWidth 32).setWidth 64).setWidth 8) = b ^^^ a := by
  ext i hi
  have h₁ : i < 32 := by omega
  have h₂ : i < 64 := by omega
  simp only [BitVec.getElem_setWidth, BitVec.getElem_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor,
    BitVec.getLsbD_eq_getElem hi, h₁, h₂, decide_true, Bool.true_and]
  exact Bool.xor_comm _ _

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `r15 + uo` and `T` at `r12`. -/
theorem xor_ok {uo n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State}
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .r15 + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 0 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .r15 + BitVec.ofNat 64 uo, n⟩ ⟨s.gpr .r12, n⟩) :
    WP isa (.seq (.block [.mov32 .r14 (.imm 0)])
      (.loop (.block [.movzx8 .rax (byteAt .r15 uo), .movzx8 .rcx (byteAt .r12 0),
        .alu32 .xor .rax (.reg .rcx), .store8 (byteAt .r12 0) .rax, .alu .add .r14 (.imm 1),
        .alu .cmp .r14 (.imm (BitVec.ofNat 32 n))]) .ne)) s
      fun t => XorInv s (s.gpr .r15 + BitVec.ofNat 64 uo) (s.gpr .r12) n t := by
  set U := s.gpr .r15 + BitVec.ofNat 64 uo
  set T := s.gpr .r12
  have hT0 : T + BitVec.ofNat 64 0 = T := BitVec.add_zero _
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : XorInv s U T 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil]⟩
  refine count_loop hn (XorInv s U T) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by rw [BitVec.add_comm, BitVec.add_sub_cancel],
      toNat_ofNat_lt (show k < 2 ^ 64 by omega), Nat.lt_irrefl, ↓reduceIte]
  refine wp_movzx8 (a := U + BitVec.ofNat 64 k) (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide) (by decide)])
    (by rw [h.rd, h.wr]; exact hinU k hk) fun t₁ u₁ => ?_
  refine wp_movzx8 (a := T + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ (by decide),
      h.other _ (by decide) (by decide) (by decide), hT0])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact InRegions.right' (hT0 ▸ houtT k hk)) fun t₂ u₂ => ?_
  refine wp_xor32r fun t₃ u₃ => ?_
  refine wp_store8 (a := T + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14]), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.other _ (by decide) (by decide) (by decide), hT0])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hT0 ▸ houtT k hk) fun t₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_addi fun t₅ u₅ => wp_cmpi fun t₆ g₆ m₆ rd₆ wr₆ _ z₆ => WP.block_nil ?_
  have h14 : t₅.gpr .r14 = BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 := by
    rw [u₅.gpr, g₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r14]
  refine ⟨⟨by rw [rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r ha hc h14' => by
      rw [g₆, u₅.other r h14', g₄, u₃.other r ha, u₂.other r hc, u₁.other r ha, h.other r ha hc h14'],
    by rw [g₆, h14, sx_one, ← ofNat_succ], ?_⟩, by rw [z₆, h14, count_zf hk hn']⟩
  have hv : (t₃.gpr .rax).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, xor_byte2, u₁.mem, rU, rT]
  have e' := writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
    (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega)
  rw [hl'] at e'
  rw [m₆, u₅.mem, m₄, hv, u₃.mem, u₂.mem, u₁.mem, h.mem, e', bytesAt_snoc', bytesAt_snoc',
    xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]

/-! ## `init`'s key and pad loops

`K₀ ⊕ ipad` is written at `P` and `K₀ ⊕ opad` at `P + B`, byte by byte: first
the key's `kl` bytes (read at `K`), then the zeros that pad it to `B`
(`Proof/Hmac/Generic/Common.lean`'s `BufMem`). -/

variable (H : Hash)

/-- Where the loops are. -/
structure LoopRegs (P K : Addr) (kl : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 + BitVec.ofNat 64 H.buf = P
  rbp : s.gpr .rbp = K
  r13 : s.gpr .r13 = BitVec.ofNat 64 kl

theorem LoopRegs.keep {P K : Addr} {kl : Nat} {s t : State} (h : LoopRegs H P K kl s)
    (hk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s.gpr r) : LoopRegs H P K kl t :=
  ⟨by rw [hk _ (by decide) (by decide) (by decide), h.r15], by rw [hk _ (by decide) (by decide) (by decide), h.rbp],
    by rw [hk _ (by decide) (by decide) (by decide), h.r13]⟩

/-- The loops' invariant, from the state `s` they start in. -/
structure KeyInv (s : State) (P K : Addr) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : BufMem H.B P (K0 s.mem K kl H.B) s.mem j t.mem

theorem xor_byte (b : Byte) (v : BitVec 32) :
    ((((b.setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem xor_byte' (b : Byte) (v : BitVec 32) :
    ((((((b.setWidth 64).setWidth 32).setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 =
      b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

/-- The regions the loops access. -/
structure LoopMem (P K : Addr) (kl : Nat) (s : State) : Prop where
  kl_le : kl ≤ H.B
  key : ∀ k < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  buf : ∀ k < 2 * H.B, InRegions s.wr (P + BitVec.ofNat 64 k) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, 2 * H.B⟩
  hB : H.B ≤ 128

theorem key_step {P K : Addr} {kl : Nat} {s : State} (hr : LoopRegs H P K kl s) (hm : LoopMem H P K kl s)
    {j : Nat} (hj : j < kl) {t : State} (h : KeyInv H s P K kl j t) :
    WP isa (.block [.movzx8 .rax (byteAt .rbp 0), .mov32 .rcx (.reg .rax),
      .alu32 .xor .rax (.imm 0x36), .store8 (byteAt .r15 H.buf) .rax, .alu32 .xor .rcx (.imm 0x5c),
      .store8 (byteAt .r15 (H.buf + H.B)) .rcx, .alu .add .r14 (.imm 1),
      .alu .cmp .r14 (.reg .r13)]) t fun t' => KeyInv H s P K kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep H h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.Sha256.X86_64.contains_offset (n := 1) (by omega) (by omega)) hc
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j) (by rw [ea_byteAt _ _ _ _ h.r14, rt.rbp, BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hm.key j hj) fun t₁ u₁ => ?_
  refine wp_mov32r fun t₂ u₂ => wp_xor32i fun t₃ u₃ => ?_
  have e14 : ∀ t' : State, t'.gpr .r14 = t.gpr .r14 → t'.gpr .r15 = t.gpr .r15 → ∀ o,
      t'.ea (byteAt .r15 o) = t.gpr .r15 + BitVec.ofNat 64 o + BitVec.ofNat 64 j := fun t' a b o => by
    rw [ea_byteAt _ _ _ j (by rw [a, h.r14]), b]
  refine wp_store8 (a := P + BitVec.ofNat 64 j)
    (by rw [e14 _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]), rt.r15])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_xor32i fun t₅ u₅ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [e14 _ (by rw [u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]) (by rw [u₅.other _ (by decide), g₄, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]), ← add_ofNat_add, rt.r15])
    (by rw [u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega))
    fun t₆ g₆ m₆ rd₆ wr₆ => ?_
  refine wp_addi fun t₇ u₇ => wp_cmp fun t₈ g₈ m₈ rd₈ wr₈ _ z₈ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t₈.gpr r = t.gpr r := fun r h1 h2 h3 => by
    rw [g₈, u₇.other r h3, g₆, u₅.other r h2, g₄, u₃.other r h1, u₂.other r h2, u₁.other r h1]
  have h14 : t₇.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [u₇.gpr, g₆, u₅.other _ (by decide), g₄, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14, sx_one, ofNat_succ]
  refine ⟨⟨by rw [rd₈, u₇.rd, rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [wr₈, u₇.wr, wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 => by rw [k r h1 h2 h3, h.other r h1 h2 h3], by rw [g₈, h14], ?_⟩, ?_⟩
  · have v₁ : (t₃.gpr .rax).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.ipad := by
      rw [u₃.gpr, u₂.other .rax (by decide), u₁.gpr, xor_byte, hbyte]; rfl
    have v₂ : (t₅.gpr .rcx).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.opad := by
      rw [u₅.gpr, g₄, u₃.other .rcx (by decide), u₂.gpr, u₁.gpr, xor_byte', hbyte]; rfl
    rw [m₈, u₇.mem, m₆, v₂, u₅.mem, m₄, v₁, u₃.mem, u₂.mem, u₁.mem]
    exact buf_write h.mem hB (by omega) hl
  · rw [z₈, h14, show t₇.gpr .r13 = BitVec.ofNat 64 kl by
      rw [u₇.other _ (by decide), g₆, u₅.other _ (by decide), g₄, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), rt.r13], sub_beq (by omega) (by omega)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {P K : Addr} {kl : Nat} {s : State} (hr : LoopRegs H P K kl s) (hm : LoopMem H P K kl s)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hz : s.zf = some (decide (kl = 0))) :
    WP isa (.ite .e (.block []) H.keyLoop) s (KeyInv H s P K kl kl) := by
  have i0 : KeyInv H s P K kl 0 s :=
    ⟨rfl, rfl, fun _ _ _ _ => rfl, h14, ⟨by simp [bytesAt], by simp [bytesAt], Frame.refl _ _⟩⟩
  refine WP.ite (decide (kl = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (KeyInv H s P K kl) (fun j hj t h => key_step H hr hm hj h) i0

/-- In the pad loop, `rax` and `rcx` hold `ipad` and `opad`. -/
structure PadInv (s₀ : State) (P K : Addr) (kl j : Nat) (t : State) : Prop extends
    KeyInv H s₀ P K kl j t where
  rax : t.gpr .rax = (0x36 : BitVec 32).setWidth 64
  rcx : t.gpr .rcx = (0x5c : BitVec 32).setWidth 64

theorem pad_step {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {t : State} (h : PadInv H s₀ P K kl j t) :
    WP isa (.block [.store8 (byteAt .r15 H.buf) .rax, .store8 (byteAt .r15 (H.buf + H.B)) .rcx,
      .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.B))]) t
      fun t' => PadInv H s₀ P K kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = H.B)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep H h.other
  refine wp_store8 (a := P + BitVec.ofNat 64 j) (by rw [ea_byteAt _ _ _ _ h.r14, rt.r15])
    (by rw [h.wr]; exact hm.buf j (by omega)) fun t₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ j (by rw [g₁, h.r14]), g₁, ← add_ofNat_add, rt.r15])
    (by rw [wr₁, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega)) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmpi fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have k : ∀ r, r ≠ .r14 → t₄.gpr r = t.gpr r := fun r h1 => by rw [g₄, u₃.other r h1, g₂, g₁]
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 j + (1 : BitVec 32).signExtend 64 := by
    rw [u₃.gpr, g₂, g₁, h.r14]
  refine ⟨⟨⟨by rw [rd₄, u₃.rd, rd₂, rd₁, h.rd], by rw [wr₄, u₃.wr, wr₂, wr₁, h.wr],
    fun r h1 h2 h3 => by rw [k r h3, h.other r h1 h2 h3], by rw [g₄, h14, sx_one, ← ofNat_succ], ?_⟩,
    by rw [k _ (by decide), h.rax], by rw [k _ (by decide), h.rcx]⟩, ?_⟩
  · have e : ∀ v : BitVec 32, ((v.setWidth 64).setWidth 8) = (0 : Byte) ^^^ v.setWidth 8 := fun v => by
      ext i hi; simp [BitVec.getElem_setWidth]
    rw [m₄, u₃.mem, m₂, m₁, g₁, h.rax, h.rcx, e, e, ← K0_ge (m := s₀.mem) (K := K) (B := H.B) hj hl]
    exact buf_write h.mem hB hj' hl
  · rw [z₄, h14, count_zf hj' (by omega)]

/-- The pad loop, skipped for a key of `B` bytes. -/
theorem pad_ok {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {t : State} (h : KeyInv H s₀ P K kl kl t) :
    WP isa (.seq (.block [.mov32 .rax (.imm 0x36), .mov32 .rcx (.imm 0x5c),
        .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.B))]) (.ite .e (.block []) H.padLoop)) t
      (KeyInv H s₀ P K kl H.B) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  refine WP.seq (wp_mov32i fun t₁ u₁ _ _ => wp_mov32i fun t₂ u₂ _ _ =>
    wp_cmpi fun t₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_)
  have i0 : PadInv H s₀ P K kl kl t₃ :=
    ⟨⟨by rw [rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₃, u₂.wr, u₁.wr, h.wr],
      fun r h1 h2 h3 => by rw [g₃, u₂.other r h2, u₁.other r h1, h.other r h1 h2 h3],
      by rw [g₃, u₂.other _ (by decide), u₁.other _ (by decide), h.r14],
      by rw [m₃, u₂.mem, u₁.mem]; exact h.mem⟩,
      by rw [g₃, u₂.other _ (by decide), u₁.gpr], by rw [g₃, u₂.gpr]⟩
  have hz : t₃.zf = some (decide (kl = H.B)) := by
    rw [z₃, u₂.other _ (by decide), u₁.other _ (by decide), h.r14, sx_ofNat (by omega),
      sub_beq (by omega) (by omega)]
  refine WP.ite (decide (kl = H.B)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0.toKeyInv
  · have : kl < H.B := by simp at h0; omega
    refine WP.mono (WP.loop (M := isa) (fun n t => ∃ j, n = H.B - j ∧ kl ≤ j ∧ j < H.B ∧ PadInv H s₀ P K kl j t)
      ?_ (H.B - kl) t₃ ⟨kl, rfl, (Nat.le_refl _), this, i0⟩) fun _ h => h
    rintro n t ⟨j, rfl, hj, hj', hb⟩
    refine WP.mono (pad_step H hr hm hj hj' hb) fun t' ⟨hb', hz'⟩ => ?_
    by_cases hl : j + 1 = H.B
    · exact .inl ⟨by simp [eval, hz', hl], hl ▸ hb'.toKeyInv⟩
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, j + 1, rfl, by omega, by omega, hb'⟩

end VG.Proof.Hmac.Generic.X86_64

/-!
# HMAC over any streaming hash function on x86-64: our caller's registers

Untrusted: everything here is checked by Lean. The six callee-saved
registers we use are stored in `scratch` after the working space of the
functions we call (`Hash.saved`), and loaded back at the end.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at ofInt_natCast contains_offset toNat_ofNat_lt)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_store wp_movm)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Hash)

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 48⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (slot H scr 0) 64 = s₀.gpr .rbx
  rbp : m.readW (slot H scr 1) 64 = s₀.gpr .rbp
  r12 : m.readW (slot H scr 2) 64 = s₀.gpr .r12
  r13 : m.readW (slot H scr 3) 64 = s₀.gpr .r13
  r14 : m.readW (slot H scr 4) 64 = s₀.gpr .r14
  r15 : m.readW (slot H scr 5) 64 = s₀.gpr .r15

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 6) :
    Region.Sub ⟨slot H scr i, 8⟩ (saveR H scr) := by
  rw [slot, ← add_ofNat_add]
  exact Proof.Sha256.X86_64.sub_offset (by omega) (by omega)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 6) (hj : j < 6) (hij : i ≠ j) (hW : H.W ≤ 64) :
    Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, slot] at h₁ h₂
  rw [← BitVec.sub_sub] at h₁ h₂
  generalize a - scr = y at h₁ h₂
  rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega)] at h₁ h₂
  have := y.isLt
  omega

theorem SavedRegs.frame {scr : Addr} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := by
  have k : ∀ i < 6, m'.readW (slot H scr i) 64 = m.readW (slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega), h.rbx], by rw [k 1 (by omega), h.rbp], by rw [k 2 (by omega), h.r12],
    by rw [k 3 (by omega), h.r13], by rw [k 4 (by omega), h.r14], by rw [k 5 (by omega), h.r15]⟩

theorem ea_slot (s : State) (b : Reg) (scr : Addr) (hb : s.gpr b = scr) (i : Nat) :
    s.ea (at_ b (8 * H.W + 8 * i)) = slot H scr i := by
  rw [ea_at, ofInt_natCast, hb]

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 48 ≤ L)
    (hW : H.W ≤ 64) {i : Nat} (hi : i < 6) : InRegions rs (slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega) (by omega)⟩

/-- Saving the registers, with `scratch` in `r8`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h8 : s.gpr .r8 = scr) (hW : H.W ≤ 64)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → Frame [saveR H scr] s.mem s'.mem →
      SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 6, InRegions t.wr (slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact slot_in H hsc hL hW hi
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ i, t.ea (at_ .r8 (8 * H.W + 8 * i)) = slot H scr i :=
    fun hg i => by rw [ea_at, ofInt_natCast, hg, h8]
  simp only [Hash.save, Hash.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_store (a := slot H scr 0) (ea rfl 0) (io rfl 0 (by omega)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := slot H scr 1) (ea g₁ 1) (io wr₁ 1 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := slot H scr 2) (ea (g₂.trans g₁) 2) (io (wr₂.trans wr₁) 2 (by omega))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := slot H scr 3) (ea (g₃.trans (g₂.trans g₁)) 3) (io (wr₃.trans (wr₂.trans wr₁)) 3 (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := slot H scr 4) (ea (g₄.trans (g₃.trans (g₂.trans g₁))) 4)
    (io (wr₄.trans (wr₃.trans (wr₂.trans wr₁))) 4 (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := slot H scr 5) (ea (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁)))) 5)
    (io (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans wr₁)))) 5 (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have g : s₆.gpr = s.gpr := g₆.trans (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁))))
  refine k s₆ g (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_ ?_
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
    have c : ∀ i < 6, (saveR H scr).Contains (slot H scr i) (64 / 8) := fun i hi => by
      rw [slot, ← add_ofNat_add]; exact contains_offset (by omega) (by omega)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _ (c 5 (by omega)))
  · have d : ∀ i j, i < 6 → j < 6 → i ≠ j → Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ :=
      fun i j hi hj hij => slot_disj H scr hi hj hij hW
    rw [m₆, m₅, m₄, m₃, m₂, m₁, g₅, g₄, g₃, g₂, g₁]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [readW_writeW_ne _ _ (d 0 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 4 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 3 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 2 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 0 1 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 1 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 1 4 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 1 3 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 1 2 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 2 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 2 4 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 2 3 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 3 5 (by omega) (by omega) (by omega)),
        readW_writeW_ne _ _ (d 3 4 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 4 5 (by omega) (by omega) (by omega)), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `r15` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h15 : s.gpr .r15 = scr) (hW : H.W ≤ 64) {s₀ : State}
    (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 6, InRegions (t.rd ++ t.wr) (slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (slot_in H hsc hL hW hi)
  have ea : ∀ {t : State}, t.gpr .r15 = scr → ∀ i, t.ea (at_ .r15 (8 * H.W + 8 * i)) = slot H scr i :=
    fun h i => by rw [ea_at, ofInt_natCast, h]
  simp only [Hash.restore, Hash.saved, List.map_cons, List.map_nil]
  refine wp_movm (a := slot H scr 0) (ea h15 0) (io rfl rfl 0 (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := slot H scr 1) (ea (by rw [u₁.other _ (by decide), h15]) 1)
    (io u₁.rd u₁.wr 1 (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := slot H scr 2) (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h15]) 2)
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := slot H scr 3) (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), h15]) 3)
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := slot H scr 4) (ea (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₁.other _ (by decide), h15]) 4)
    (io (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))) (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))) 4
      (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := slot H scr 5) (ea (by rw [u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h15]) 5)
    (io (u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))))
      (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr)))) 5 (by omega)) fun s₆ u₆ => ?_
  refine WP.block_nil ⟨by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    ?_, fun r hr => ?_⟩
  · have hm : ∀ t : State, t.mem = s.mem → ∀ i, t.mem.readW (slot H scr i) 64 = s.mem.readW (slot H scr i) 64 :=
      fun t h i => by rw [h]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, hs.rbx]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, hs.rbp]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        hs.r12]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hs.r13]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r14]
    · rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r15]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]

end VG.Proof.Hmac.Generic.X86_64

/-!
# HMAC over any streaming hash function on x86-64: `init`, correct

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Hmac.Generic.X86_64.Init

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64
open VG.Proof.Hmac.Generic.Common (bytesAt_prefix_congr take_map_xor add_ofNat_add inRegions_of_sub
  off_disj off_disj0 covers_one sub_of_off sub_of_self bytes_keep K0 K0_length)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi wp_test)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The padded keys. -/
abbrev P : Addr := scr s₀ + BitVec.ofNat 64 H.buf
abbrev bufR : Region := ⟨P (H := H) s₀, 2 * H.B⟩
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  ret_i : (retR s₀).Disjoint (inR (H := H) s₀)
  ret_o : (retR s₀).Disjoint (outR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + 2 * H.B ≤ 8 * sc
  hB : H.B ≤ 128
  hW : H.W ≤ 64
  hS : H.S ≤ 256

theorem pre_of {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.buf + 2 * H.B ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit, hH.hBB, hH.hW,
    hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem buf_le : H.buf + 2 * H.B ≤ 8 * sc := hp.fits

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; simp only [Hash.buf] at this; exact sub_sc hp (by omega) (by omega)

theorem buf_sub : Region.Sub (bufR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hB; have := hp.hW
  exact sub_offset hp.fits (by simp only [Hash.buf] at *; omega)

omit hp in
theorem padI_sub : Region.Sub ⟨P (H := H) s₀, H.B⟩ (bufR (H := H) s₀) := Region.sub_prefix (by omega)

theorem padO_sub : Region.Sub ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (bufR (H := H) s₀) :=
  sub_offset (by omega) (by have := hp.hB; omega)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 48) (by omega) (by omega)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 48) (n := 2 * H.B) (by omega) (by omega)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 48) (b := 8 * H.W + 48) (n := 2 * H.B) (by omega) (by omega)
    (by omega)

omit hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r12 : s.gpr .r12 = out s₀
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

/-- `KR` survives changes to other registers, and to memory away from the
save area and the return address. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rsp, .rbx, .r12, .r15], s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (retR s₀).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r15, h.saved.frame H hf hs,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem (kp s₀) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) s₀) := by
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  have hL : 8 * H.W + 48 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  refine WP.seq (save_ok H (scr := scr s₀) rfl hp.hW hsc hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_)
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov32i fun s₇ u₇ _ _ => wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => WP.block_nil ?_
  have k₈ : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13, .r14] → s₈.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈, u₇.other r hr.2.2.2.2.2, u₆.other r hr.2.2.2.2.1, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1,
      u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have r8 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → ∀ t : State,
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s₈.gpr r) → t.gpr r = s₈.gpr r :=
    fun r _ _ _ t h => h r ‹_› ‹_› ‹_›
  have hbx : s₈.gpr .rbx = inn s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have h12 : s₈.gpr .r12 = out s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  have h15 : s₈.gpr .r15 = scr s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have hbp : s₈.gpr .rbp = kp s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have h13 : s₈.gpr .r13 = s₀.gpr .rcx := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have h14 : s₈.gpr .r14 = BitVec.ofNat 64 0 := by rw [g₈, u₇.gpr]; rfl
  have hm₈ : s₈.mem = s₁.mem := by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hrd : s₈.rd = s₀.rd := by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have hwr : s₈.wr = s₀.wr := by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have hz : s₈.zf = some (decide (kl s₀ = 0)) := by
    rw [z₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁, BitVec.and_self]
    congr 1
    by_cases h : kl s₀ = 0
    · simp [h, BitVec.eq_of_toNat_eq (show (s₀.gpr .rcx).toNat = (0 : BitVec 64).toNat from h)]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'; exact h (by show (s₀.gpr .rcx).toNat = 0; rw [h']; rfl)
  have hB := hp.hB
  have hr : LoopRegs H (P (H := H) s₀) (kp s₀) (kl s₀) s₈ :=
    ⟨by rw [h15], hbp, by rw [h13, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hm : LoopMem H (P (H := H) s₀) (kp s₀) (kl s₀) s₈ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (s₀.gpr .rcx).isLt hk |>.elim
          fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega) hk,
      hp.k_s.sub_right (buf_sub hp), hB⟩
  refine WP.seq (WP.mono (key_ok H hr hm h14 hz) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₈.mem := hm₈ ▸ f₁
  have eK : K0 s₈.mem (kp s₀) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp))) (by
      exact Nat.le_of_lt (s₀.gpr .rcx).isLt) hi
  have ft : Frame [saveR H (scr s₀), bufR (H := H) s₀] s₀.mem t.mem :=
    (fk.mono (by simp)).trans (ht.mem.frame.mono (by simp))
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s₈.gpr r := ht.other
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [hg _ (by decide) (by decide) (by decide),
      k₈ _ (by simp)], by rw [hg _ (by decide) (by decide) (by decide), hbx],
    by rw [hg _ (by decide) (by decide) (by decide), h12], by rw [hg _ (by decide) (by decide) (by decide), h15],
    (sv₁.frame H (hm₈ ▸ ht.mem.frame) (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp)),
    ft.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_s.sub_right (save_sub hp)
      · exact hp.ret_s.sub_right (buf_sub hp)) (by decide)⟩, ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem state_disj {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p, H.S⟩ ∧ (retR s₀).Disjoint ⟨p, H.S⟩ := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.stk_i, hp.ret_i⟩
  · exact ⟨hp.o_s, hp.stk_o, hp.ret_o⟩

theorem state_in {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨p, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem initArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p) :
    WP isa (.block [.mov .rdi (.reg st)]) s fun t => KR (H := H) s₀ t ∧ t.gpr .rdi = p ∧ t.mem = s.mem :=
  wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨hk.keep (by rw [u₁.rd]) (by rw [u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact u₁.other _ (by decide))
    (rs := []) (by rw [u₁.mem]; exact Frame.refl _ _) (by simp) (by simp), by rw [u₁.gpr, hs], u₁.mem⟩

/-- The regions of `init`'s call, from `KR`. -/
theorem initCall_args {t : State} (hk : KR (H := H) s₀ t) {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    Covers [⟨p, H.S⟩] t.wr ∧ (below (t.gpr .rsp) 16).Disjoint ⟨p, H.S⟩ := by
  obtain ⟨_, dK, _⟩ := state_disj hp hpR
  exact ⟨by rw [hk.wr]; exact covers_one (state_in hp hpR), by rw [hk.rsp]; exact dK⟩

theorem initCall_ok {t : State} (hk : KR (H := H) s₀ t) {p : Addr} (hd : t.gpr .rdi = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] t.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (.call H.initN H.initC) t Q := by
  obtain ⟨dS, _, dR⟩ := state_disj hp hpR
  obtain ⟨c, k⟩ := initCall_args hp hk hpR
  refine init_call hH hd c k fun s' ha hr => ?_
  have f := ha.frame
  rw [hk.rsp] at f
  refine hQ s' (hk.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_ ?_) f hr
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (dS.symm.sub_left (save_sub hp))
    · exact (hp.stk_s.symm.sub_left (save_sub hp))
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dR
    · exact (stk_ret (s₀ := s₀)).symm

theorem callInit_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.callInit st) s Q :=
  WP.seq (WP.mono (initArgs_ok hk hs) fun _ ⟨k, d, m⟩ =>
    initCall_ok hH hp k d hpR fun s' k' f r => hQ s' k' (m ▸ f) r)

/-- The arguments of `init`'s calls of `update`. -/
abbrev dO (s₀ : State) (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} (hst : st = .rbx ∨ st = .r12) {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block (([.mov .rdi (.reg st)] : List Instr) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 0))] : List Instr) ++
        VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++
        ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.B)), .mov .r8 (.reg .r15)] : List Instr))) s fun t =>
      KR (H := H) s₀ t ∧ UpdArgs hH t p (dO s₀ o) (scr s₀) H.B ∧ t.gpr .rsi = 0 ∧ t.mem = s.mem := by
  obtain ⟨dS, dK, _⟩ := state_disj hp hpR
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o < 2 ^ 31 := by omega
  have dsub : Region.Sub ⟨dO s₀ o, H.B⟩ (bufR (H := H) s₀) := by
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [dO, ← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨dO s₀ o, H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  have hstr : st ≠ .rdi ∧ st ≠ .rsi ∧ st ≠ .rdx ∧ st ≠ .rcx ∧ st ≠ .r8 := by
    rcases hst with rfl | rfl <;> decide
  simp only [VG.Impl.Hmac.Generic.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_mov32i fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ =>
    wp_mov32i fun s₅ u₅ _ _ => wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have hsp : s₆.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hk.rsp]
  have h15 : s.gpr .r15 = scr s₀ := hk.r15
  have hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₆ : KR (H := H) s₀ s₆ := hk.keep (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)
  refine ⟨k₆, ?_, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]; rfl, hm⟩
  exact
    { rdi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs]
      rdx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
          u₂.other _ (by decide), u₁.other _ (by decide), h15, sx_ofNat ho']
      rcx := by rw [u₆.other _ (by decide), u₅.gpr, zx_ofNat (by omega), toNat_ofNat_lt (by omega)]
      r8 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), h15]
      cd := by
        rw [k₆.rd, k₆.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.wr]; simp) (by omega)
      cw := by
        rw [k₆.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨p, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      stk_st := by rw [hsp]; exact dK
      stk_d := by rw [hsp]; exact hp.stk_s.sub_right dsc
      stk_sc := by rw [hsp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) {p d : Addr} (hpR : p = inn s₀ ∨ p = out s₀)
    (ha : UpdArgs hH t p d (scr s₀) H.B) (hsi : t.gpr .rsi = 0) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt t.mem d H.B)) → Q s') :
    WP isa (.call H.updN H.updC) t Q := by
  obtain ⟨dS, _, dR⟩ := state_disj hp hpR
  have hB := hp.hB
  refine upd_call hH ha (by omega) fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.rsp] at f
  refine hQ s' (hk.keep ha'.rd ha'.wr (fun r hr => ha'.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_ ?_) f
    fun hr => hpost [] hr (by rw [hsi]; rfl)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact dS.symm.sub_left (save_sub hp)
    · exact (cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (save_sub hp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact dR
    · exact hp.ret_s.sub_right (cal_sub hH hp)
    · exact (stk_ret (s₀ := s₀)).symm

theorem callUpd_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} (hst : st = .rbx ∨ st = .r12) {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt s.mem (scr s₀ + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [.mov .rdi (.reg st)] 0 o H.B) s Q :=
  WP.seq (WP.mono (updArgs_ok hH hp hk hst hs hpR ho) fun _ ⟨k, a, si, m⟩ =>
    updCall_ok hH hp k hpR a si fun s' k' f r => hQ s' k' (m ▸ f) (m ▸ r))

/-! ## Memory kept by the calls -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.Common.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega,
    ↓reduceIte]

/-! ## Correctness -/

theorem correct :
    WP isa H.init s₀ fun s' => gprPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits
  simp only [Hash.buf] at hf
  -- Where things are.
  have dIS : Region.Disjoint ⟨P (H := H) s₀, H.B⟩ (inR (H := H) s₀) :=
    hp.i_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dIO : Region.Disjoint ⟨P (H := H) s₀, H.B⟩ (outR (H := H) s₀) :=
    hp.o_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dOS : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (inR (H := H) s₀) :=
    hp.i_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dOO : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (outR (H := H) s₀) :=
    hp.o_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dIK : Region.Disjoint ⟨P (H := H) s₀, H.B⟩ (stkR s₀) :=
    hp.stk_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dOK : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (stkR s₀) :=
    hp.stk_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dOC : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (calR hH s₀) :=
    (cal_buf hH hp).symm.sub_left (padO_sub hp)
  have eO : scr s₀ + BitVec.ofNat 64 (H.buf + H.B) = P (H := H) s₀ + BitVec.ofNat 64 H.B := by
    rw [P, add_ofNat_add]
  refine WP.seq (WP.mono (keys_ok sc hp) fun s₁ h₁ => ?_)
  refine WP.seq (callInit_ok hH hp h₁.kr (st := .rbx) h₁.kr.rbx (.inl rfl) fun s₂ k₂ f₂ r₂ => ?_)
  have bI₂ := (bytes_keep f₂ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega)).trans h₁.bufI
  have bO₂ := (bytes_keep f₂ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega)).trans h₁.bufO
  refine WP.seq (callUpd_ok hH hp k₂ (.inl rfl) k₂.rbx (.inl rfl) (.inl rfl) fun s₃ k₃ f₃ r₃ => ?_)
  have rI₃ := r₃ r₂
  rw [List.nil_append, bI₂] at rI₃
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> with_reducible assumption)
    (by omega)).trans bO₂
  refine WP.seq (callInit_ok hH hp k₃ (st := .r12) k₃.r12 (.inr rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := repr_keep hH f₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.stk_i.symm) rI₃
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega)).trans bO₃
  refine WP.seq (callUpd_ok hH hp k₄ (.inr rfl) k₄.r12 (.inr rfl) (.inr rfl) fun s₅ k₅ f₅ r₅ => ?_)
  have rO₅ := r₅ r₄
  rw [List.nil_append, eO, bO₄] at rO₅
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.stk_i.symm) rI₄
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₅.wr := by rw [k₅.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₅.r15 hW k₅.saved hsc (by omega)) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  · rw [hm, k₅.ret]
  · show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
    rw [hm, blockKey_eq hH hp]
    exact ⟨rI₅, rO₅⟩

end

end VG.Proof.Hmac.Generic.X86_64.Init
