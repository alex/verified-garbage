import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Hash
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function on AArch64: the byte loops

As on x86-64 (`Proof/Hmac/Generic/X86_64/Init.lean`, with the lemmas on byte
lists and memory of `Proof/Hmac/Generic/Common.lean`): the byte copy (`copy`),
used for states, digests and `U`; the exclusive-or of `U` into `T`; and `init`'s
loops that write `K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each counts `x24` up from 0, and
computes the bytes left into `x11`, on which it branches.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy left)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeW8_apply)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_add wp_sub wp_addImm wp_movz wp_ldrb wp_strb
  eval_nonzero eval_zero ofNat_succ)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint add_ofNat_ne
  add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge xorBytes_snoc xorBytes_length'
  InRegions.right')
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Proof.MdStream.AArch64.Upd.write64 _ _ _))

end

theorem movz_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_nat

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_nat

theorem ofNat_ne_zero {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = decide (a ≠ 0) := by
  by_cases ha : a = 0
  · subst ha; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => ha (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this)
    rw [show (BitVec.ofNat 64 a != 0) = true from bne_iff_ne.mpr this]; simp [ha]

/-- `x11` after `movz x11, n; sub x11, x11, x24` with `x24 = k ≤ n`. -/
theorem left_val {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth 64 - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  rw [movz_ofNat hn, sub_ofNat' hk (by omega_nat)]

/-- The registers the loops write. -/
abbrev clob : List Reg := [.x9, .x10, .x11, .x12, .x13, .x24]

theorem nm {r : Reg} (h : r ∉ clob) (x : Reg) (hx : x ∈ clob := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `x11 ≠ 0` that runs its body `n > 0` times, with
`x11` the iterations left after each. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x .x11)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' h' => ?_
  obtain ⟨hi', hx⟩ := h'
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (n - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, hx, ofNat_ne_zero (by omega_nat)]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp; omega_nat, n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

/-! ## `copy` -/

/-- After `k` bytes of `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  x24 : t.gpr .x24 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ∉ clob) (hd : dst ∉ clob)
    {so d n : Nat} (hso : so < 4096) (hdo : d < 4096) (hn : 0 < n) (hn' : n < 2 ^ 16) {s : State}
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr src + BitVec.ofNat 64 so, n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      Copied s (s.gpr dst + BitVec.ofNat 64 d) (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 so) n) t := by
  set A := s.gpr src + BitVec.ofNat 64 so
  set B := s.gpr dst + BitVec.ofNat 64 d
  refine WP.seq (wp_movz fun s₀ u₀ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, u₀.sp, fun r hr => u₀.other r (nm hr .x24), by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (count_loop hn (by omega_nat) (CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) hso
    (by rw [u₁.gpr, h.other src hs, h.x24]; simp only [A]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) hdo
    (by rw [u₃.gpr, u₂.other dst (nm hd .x9), u₁.other dst (nm hd .x12), h.other dst hd,
      u₂.other .x24 (by decide), u₁.other .x24 (by decide), h.x24]; simp only [B]; ac_rfl)
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_addImm (by decide) fun t₅ u₅ => wp_movz fun t₆ u₆ => wp_sub fun t₇ u₇ => WP.block_nil ?_
  have h24 : t₅.gpr .x24 = BitVec.ofNat 64 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x24]
    exact (ofNat_succ k).symm
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₇.other r (nm hr .x11), u₆.other r (nm hr .x11), u₅.other r (nm hr .x24), m₄.gpr,
        u₃.other r (nm hr .x13), u₂.other r (nm hr .x9), u₁.other r (nm hr .x12), h.other r hr],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), h24], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₃.gpr .x9).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_nat)
    rw [hl] at e'
    rw [u₇.mem, u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), h24, left_val (by omega_nat) hn']

/-! ## The exclusive-or of `U` into `T` -/

theorem xor_byte2 (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8) = b ^^^ a := by
  ext i hi
  simp [BitVec.getElem_xor, Bool.xor_comm]

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  x24 : t.gpr .x24 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `x23 + uo` and `T` at `x20`. -/
theorem xor_ok {uo n : Nat} (huo : uo < 4096) (hn : 0 < n) (hn' : n < 2 ^ 16) {s : State}
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .x23 + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr .x23 + BitVec.ofNat 64 uo, n⟩ ⟨s.gpr .x20, n⟩) :
    WP isa (.seq (.block [.movz .x .x24 0 0])
      (.loop (.block (([.add .x .x12 .x23 .x24, .ldrb .x9 .x12 uo, .add .x .x13 .x20 .x24,
        .ldrb .x10 .x13 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x13 0, .addImm .x .x24 .x24 1] : List Instr) ++
        left n)) (.nonzero .x .x11))) s
      fun t => XorInv s (s.gpr .x23 + BitVec.ofNat 64 uo) (s.gpr .x20) n t := by
  set U := s.gpr .x23 + BitVec.ofNat 64 uo
  set T := s.gpr .x20
  refine WP.seq (wp_movz fun s₀ u₀ => WP.block_nil ?_)
  have i0 : XorInv s U T 0 s₀ :=
    ⟨u₀.rd, u₀.wr, u₀.sp, fun r hr => u₀.other r (nm hr .x24), by rw [u₀.gpr]; rfl,
      by rw [u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil]⟩
  refine count_loop hn (by omega_nat) (XorInv s U T) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by rw [BitVec.add_comm, BitVec.add_sub_cancel],
      toNat_ofNat_lt (show k < 2 ^ 64 by omega_nat), Nat.lt_irrefl, ↓reduceIte]
  have g23 := h.other .x23 (by decide)
  have g20 := h.other .x20 (by decide)
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := U + BitVec.ofNat 64 k) huo (by rw [u₁.gpr, g23, h.x24]; simp only [U]; ac_rfl)
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₂ u₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  have a₃ : t₃.gpr .x13 + BitVec.ofNat 64 0 = T + BitVec.ofNat 64 k := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g20, h.x24, BitVec.add_zero]
  refine wp_ldrb (a := T + BitVec.ofNat 64 k) (by decide) a₃
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact InRegions.right' (houtT k hk))
    fun t₄ u₄ => ?_
  refine wp_eor fun t₅ u₅ => ?_
  refine wp_strb (a := T + BitVec.ofNat 64 k) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a₃)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact houtT k hk) fun t₆ m₆ => ?_
  refine wp_addImm (by decide) fun t₇ u₇ => wp_movz fun t₈ u₈ => wp_sub fun t₉ u₉ => WP.block_nil ?_
  have h24 : t₇.gpr .x24 = BitVec.ofNat 64 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.x24]
    exact (ofNat_succ k).symm
  refine ⟨⟨by rw [u₉.rd, u₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₉.sp, u₈.sp, u₇.sp, m₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₉.other r (nm hr .x11), u₈.other r (nm hr .x11), u₇.other r (nm hr .x24), m₆.gpr,
        u₅.other r (nm hr .x9), u₄.other r (nm hr .x10), u₃.other r (nm hr .x13),
        u₂.other r (nm hr .x9), u₁.other r (nm hr .x12), h.other r hr],
    by rw [u₉.other _ (by decide), u₈.other _ (by decide), h24], ?_⟩, ?_⟩
  · have hv : (t₅.gpr .x9).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
      rw [u₅.gpr, u₄.gpr, u₄.other .x9 (by decide), u₃.other .x9 (by decide), u₂.gpr, u₃.mem, u₂.mem,
        u₁.mem, xor_byte2, rU, rT]
    have e' := writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega_nat)
    rw [hl'] at e'
    rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, hv, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem, e',
      bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), h24, left_val (by omega_nat) hn']

/-! ## `init`'s key and pad loops

`K₀ ⊕ ipad` is written at `P` and `K₀ ⊕ opad` at `P + B`, byte by byte (as
on x86-64, `BufMem`): first the key's `kl` bytes (read at `K`), then the
zeros that pad it to `B`. -/

variable (H : Hash)

/-- Where the loops are, and the pads. -/
structure LoopRegs (P K : Addr) (kl : Nat) (s : State) : Prop where
  x23 : s.gpr .x23 + BitVec.ofNat 64 H.buf = P
  x21 : s.gpr .x21 = K
  x22 : s.gpr .x22 = BitVec.ofNat 64 kl
  x14 : s.gpr .x14 = (0x36 : BitVec 16).setWidth 64
  x15 : s.gpr .x15 = (0x5c : BitVec 16).setWidth 64

theorem LoopRegs.keep {P K : Addr} {kl : Nat} {s t : State} (h : LoopRegs H P K kl s)
    (hk : ∀ r ∉ clob, t.gpr r = s.gpr r) : LoopRegs H P K kl t :=
  ⟨by rw [hk _ (by decide), h.x23], by rw [hk _ (by decide), h.x21], by rw [hk _ (by decide), h.x22],
    by rw [hk _ (by decide), h.x14], by rw [hk _ (by decide), h.x15]⟩

/-- The loops' invariant, from the state `s` they start in. -/
structure KeyInv (s : State) (P K : Addr) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  x24 : t.gpr .x24 = BitVec.ofNat 64 j
  mem : BufMem H.B P (K0 s.mem K kl H.B) s.mem j t.mem

/-- The regions the loops access, and the sizes. -/
structure LoopMem (P K : Addr) (kl : Nat) (s : State) : Prop where
  kl_le : kl ≤ H.B
  key : ∀ k < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  buf : ∀ k < 2 * H.B, InRegions s.wr (P + BitVec.ofNat 64 k) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, 2 * H.B⟩
  hB : H.B ≤ 128
  hbuf : H.buf + H.B < 4096

theorem pad_byte (b : Byte) (v : BitVec 16) :
    ((b.setWidth 64 ^^^ v.setWidth 64).setWidth 8) = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem zero_pad (v : BitVec 16) : (v.setWidth 64).setWidth 8 = (0 : Byte) ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth]

theorem key_step {P K : Addr} {kl : Nat} {s : State} (hr : LoopRegs H P K kl s) (hm : LoopMem H P K kl s)
    {j : Nat} (hj : j < kl) {t : State} (h : KeyInv H s P K kl j t) :
    WP isa (.block [.add .x .x13 .x21 .x24, .ldrb .x9 .x13 0, .add .x .x12 .x23 .x24,
      .logic .eor .x .x10 .x9 .x14, .strb .x10 .x12 H.buf, .logic .eor .x .x10 .x9 .x15,
      .strb .x10 .x12 (H.buf + H.B), .addImm .x .x24 .x24 1, .sub .x .x11 .x22 .x24]) t
      fun t' => KeyInv H s P K kl (j + 1) t' ∧ t'.gpr .x11 = BitVec.ofNat 64 (kl - (j + 1)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hbuf := hm.hbuf
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega_nat
  have rt := hr.keep H h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.MdStream.AArch64.contains_offset (n := 1) (by omega_nat) (by omega_nat)) hc
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.gpr, rt.x21, h.x24, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hm.key j hj) fun t₂ u₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  have a12 : ∀ o, t₃.gpr .x12 + BitVec.ofNat 64 o = t.gpr .x23 + BitVec.ofNat 64 o + BitVec.ofNat 64 j :=
    fun o => by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.x24]; ac_rfl
  refine wp_eor fun t₄ u₄ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega_nat)
    (by rw [u₄.other _ (by decide), a12, rt.x23])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega_nat)) fun t₅ m₅ => ?_
  refine wp_eor fun t₆ u₆ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), a12, ← add_ofNat_add, rt.x23])
    (by rw [u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega_nat))
    fun t₇ m₇ => ?_
  refine wp_addImm (by decide) fun t₈ u₈ => wp_sub fun t₉ u₉ => WP.block_nil ?_
  have k : ∀ r ∉ clob, t₉.gpr r = t.gpr r := fun r hr' => by
    rw [u₉.other r (nm hr' .x11), u₈.other r (nm hr' .x24), m₇.gpr, u₆.other r (nm hr' .x10), m₅.gpr,
      u₄.other r (nm hr' .x10), u₃.other r (nm hr' .x12), u₂.other r (nm hr' .x9),
      u₁.other r (nm hr' .x13)]
  have h24 : t₈.gpr .x24 = BitVec.ofNat 64 (j + 1) := by
    rw [u₈.gpr, m₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.x24]
    exact (ofNat_succ j).symm
  refine ⟨⟨by rw [u₉.rd, u₈.rd, m₇.rd, u₆.rd, m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₉.wr, u₈.wr, m₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₉.sp, u₈.sp, m₇.sp, u₆.sp, m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr' => by rw [k r hr', h.other r hr'], by rw [u₉.other _ (by decide), h24], ?_⟩, ?_⟩
  · have x9 : t₃.gpr .x9 = (t.mem (K + BitVec.ofNat 64 j)).setWidth 64 := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
    have v₁ : (t₄.gpr .x10).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.ipad := by
      rw [u₄.gpr, x9, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), rt.x14,
        pad_byte, hbyte]; rfl
    have v₂ : (t₆.gpr .x10).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.opad := by
      rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), x9, u₄.other .x15 (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), rt.x15, pad_byte, hbyte]; rfl
    rw [u₉.mem, u₈.mem, m₇.mem, v₂, u₆.mem, m₅.mem, v₁, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact buf_write h.mem hB (by omega_nat) hl
  · rw [u₉.gpr, u₈.other _ (by decide), h24, m₇.gpr, u₆.other _ (by decide), m₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      rt.x22, sub_ofNat' (by omega_nat) (by omega_nat)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {P K : Addr} {kl : Nat} {s : State} (hr : LoopRegs H P K kl s) (hm : LoopMem H P K kl s)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 0) :
    WP isa (.ite (.zero .x .x22) (.block []) H.keyLoop) s (KeyInv H s P K kl kl) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have i0 : KeyInv H s P K kl 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, h24, ⟨by simp [bytesAt], by simp [bytesAt], Frame.refl _ _⟩⟩
  have hz : isa.eval (.zero .x .x22) s = some (decide (kl = 0)) := by
    show VG.AArch64.eval (.zero .x .x22) s = _
    rw [eval_zero, hr.x22, Proof.MdStream.AArch64.ofNat_beq_zero (by omega_nat)]
  refine WP.ite (decide (kl = 0)) hz (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega_nat
    exact count_loop this (by omega_nat) (KeyInv H s P K kl) (fun j hj t h => key_step H hr hm hj h) i0

theorem pad_step {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {t : State} (h : KeyInv H s₀ P K kl j t) :
    WP isa (.block (([.add .x .x12 .x23 .x24, .strb .x14 .x12 H.buf, .strb .x15 .x12 (H.buf + H.B),
      .addImm .x .x24 .x24 1] : List Instr) ++ left H.B)) t
      fun t' => KeyInv H s₀ P K kl (j + 1) t' ∧ t'.gpr .x11 = BitVec.ofNat 64 (H.B - (j + 1)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hbuf := hm.hbuf
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega_nat
  have rt := hr.keep H h.other
  refine wp_add fun t₁ u₁ => ?_
  have a12 : ∀ o, t₁.gpr .x12 + BitVec.ofNat 64 o = t.gpr .x23 + BitVec.ofNat 64 o + BitVec.ofNat 64 j :=
    fun o => by rw [u₁.gpr, h.x24]; ac_rfl
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega_nat) (by rw [a12, rt.x23])
    (by rw [u₁.wr, h.wr]; exact hm.buf j (by omega_nat)) fun t₂ m₂ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [m₂.gpr, a12, ← add_ofNat_add, rt.x23])
    (by rw [m₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega_nat)) fun t₃ m₃ => ?_
  refine wp_addImm (by decide) fun t₄ u₄ => wp_movz fun t₅ u₅ => wp_sub fun t₆ u₆ => WP.block_nil ?_
  have h24 : t₄.gpr .x24 = BitVec.ofNat 64 (j + 1) := by
    rw [u₄.gpr, m₃.gpr, m₂.gpr, u₁.other _ (by decide), h.x24]
    exact (ofNat_succ j).symm
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, m₃.rd, m₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, m₃.wr, m₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, m₃.sp, m₂.sp, u₁.sp, h.sp],
    fun r hr' => by
      rw [u₆.other r (nm hr' .x11), u₅.other r (nm hr' .x11), u₄.other r (nm hr' .x24), m₃.gpr, m₂.gpr,
        u₁.other r (nm hr' .x12), h.other r hr'],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), h24], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃.mem, m₂.gpr, m₂.mem, u₁.mem, u₁.other _ (by decide),
      u₁.other _ (by decide), rt.x14, rt.x15, zero_pad, zero_pad,
      ← K0_ge (m := s₀.mem) (K := K) (B := H.B) hj hl]
    exact buf_write h.mem hB hj' hl
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), h24, left_val (by omega_nat) (by omega_nat)]

/-- The pad loop, skipped for a key of `B` bytes. -/
theorem pad_ok {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {t : State} (h : KeyInv H s₀ P K kl kl t) :
    WP isa (.seq (.block (left H.B)) (.ite (.zero .x .x11) (.block []) H.padLoop)) t
      (KeyInv H s₀ P K kl H.B) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  refine WP.seq (wp_movz fun t₁ u₁ => wp_sub fun t₂ u₂ => WP.block_nil ?_)
  have i0 : KeyInv H s₀ P K kl kl t₂ :=
    ⟨by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], by rw [u₂.sp, u₁.sp, h.sp],
      fun r hr' => by rw [u₂.other r (nm hr' .x11), u₁.other r (nm hr' .x11), h.other r hr'],
      by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.x24], by rw [u₂.mem, u₁.mem]; exact h.mem⟩
  have hz : isa.eval (.zero .x .x11) t₂ = some (decide (kl = H.B)) := by
    show VG.AArch64.eval (.zero .x .x11) t₂ = _
    rw [eval_zero, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.x24, left_val hkl (by omega_nat),
      Proof.MdStream.AArch64.ofNat_beq_zero (by omega_nat)]
    congr 1; exact decide_eq_decide.mpr (by omega_nat)
  refine WP.ite (decide (kl = H.B)) hz (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0
  · have : kl < H.B := by simp at h0; omega_nat
    have := count_loop (n := H.B - kl) (by omega_nat) (by omega_nat) (fun k t => KeyInv H s₀ P K kl (kl + k) t)
      (fun k hk t hk' => WP.mono (pad_step H hr hm (j := kl + k) (by omega_nat) (by omega_nat) hk')
        fun t' ⟨a, b⟩ => ⟨by rw [← Nat.add_assoc]; exact a, by rw [b]; exact congrArg (BitVec.ofNat _) (by omega_nat)⟩)
      (s := t₂) (by simpa using i0)
    rw [show kl + (H.B - kl) = H.B by omega_nat] at this
    exact this

end VG.Proof.Hmac.Generic.AArch64

/-!
# HMAC over any streaming hash function on AArch64: our caller's registers

As on x86-64 (`Proof/Hmac/Generic/X86_64/Init.lean`): the six callee-saved
registers we use, and our return address `x30`, are stored in `scratch` after
the working space of the functions we call (`Hash.saved`), and loaded back at
the end, `x23` (which holds `scratch`) last.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.MdStream.AArch64 (contains_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_str wp_ldr)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x30, .x23]

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 56⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  x19 : m.readW (slot H scr 0) 64 = s₀.gpr .x19
  x20 : m.readW (slot H scr 1) 64 = s₀.gpr .x20
  x21 : m.readW (slot H scr 2) 64 = s₀.gpr .x21
  x22 : m.readW (slot H scr 3) 64 = s₀.gpr .x22
  x24 : m.readW (slot H scr 4) 64 = s₀.gpr .x24
  x30 : m.readW (slot H scr 5) 64 = s₀.gpr .x30
  x23 : m.readW (slot H scr 6) 64 = s₀.gpr .x23

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 7) :
    Region.Sub ⟨slot H scr i, 8⟩ (saveR H scr) := by
  rw [slot, ← add_ofNat_add]
  exact Proof.MdStream.AArch64.sub_offset (by omega_nat) (by omega_nat)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 7) (hj : j < 7) (hij : i ≠ j) (hW : H.W ≤ 1024) :
    Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, slot] at h₁ h₂
  rw [← BitVec.sub_sub] at h₁ h₂
  generalize a - scr = y at h₁ h₂
  rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega_nat)] at h₁ h₂
  have := y.isLt
  omega_nat

theorem SavedRegs.frame {scr : Addr} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := by
  have k : ∀ i < 7, m'.readW (slot H scr i) 64 = m.readW (slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega_nat), h.x19], by rw [k 1 (by omega_nat), h.x20], by rw [k 2 (by omega_nat), h.x21],
    by rw [k 3 (by omega_nat), h.x22], by rw [k 4 (by omega_nat), h.x24], by rw [k 5 (by omega_nat), h.x30],
    by rw [k 6 (by omega_nat), h.x23]⟩

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 56 ≤ L)
    (hW : H.W ≤ 1024) {i : Nat} (hi : i < 7) : InRegions rs (slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega_nat) (by omega_nat)⟩

theorem slot_eq (scr : Addr) {o : Nat} (i : Nat) (h : o = 8 * H.W + 8 * i) :
    scr + BitVec.ofNat 64 o = slot H scr i := by rw [h]

/-- Saving the registers, with `scratch` in `x4`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h4 : s.gpr .x4 = scr) (hW : H.W ≤ 1024)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 7, InRegions t.wr (slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact slot_in H hsc hL hW hi
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega_nat
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x4 + BitVec.ofNat 64 o = slot H scr i := fun hg o i h => by rw [hg, h4, h]
  simp only [Hash.save, Hash.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_str (a := slot H scr 0) (by have := ho 0 (by omega_nat); omega_nat) (ea rfl 0 (by omega_nat))
    (io rfl 0 (by omega_nat)) fun s₁ m₁ => ?_
  refine wp_str (a := slot H scr 1) (by have := ho 1 (by omega_nat); omega_nat) (ea m₁.gpr 1 (by omega_nat))
    (io m₁.wr 1 (by omega_nat)) fun s₂ m₂ => ?_
  have g₂ : s₂.gpr = s.gpr := m₂.gpr.trans m₁.gpr
  have w₂ : s₂.wr = s.wr := m₂.wr.trans m₁.wr
  refine wp_str (a := slot H scr 2) (by have := ho 2 (by omega_nat); omega_nat) (ea g₂ 2 (by omega_nat))
    (io w₂ 2 (by omega_nat)) fun s₃ m₃ => ?_
  have g₃ : s₃.gpr = s.gpr := m₃.gpr.trans g₂
  have w₃ : s₃.wr = s.wr := m₃.wr.trans w₂
  refine wp_str (a := slot H scr 3) (by have := ho 3 (by omega_nat); omega_nat) (ea g₃ 3 (by omega_nat))
    (io w₃ 3 (by omega_nat)) fun s₄ m₄ => ?_
  have g₄ : s₄.gpr = s.gpr := m₄.gpr.trans g₃
  have w₄ : s₄.wr = s.wr := m₄.wr.trans w₃
  refine wp_str (a := slot H scr 4) (by have := ho 4 (by omega_nat); omega_nat) (ea g₄ 4 (by omega_nat))
    (io w₄ 4 (by omega_nat)) fun s₅ m₅ => ?_
  have g₅ : s₅.gpr = s.gpr := m₅.gpr.trans g₄
  have w₅ : s₅.wr = s.wr := m₅.wr.trans w₄
  refine wp_str (a := slot H scr 5) (by have := ho 5 (by omega_nat); omega_nat) (ea g₅ 5 (by omega_nat))
    (io w₅ 5 (by omega_nat)) fun s₆ m₆ => ?_
  have g₆ : s₆.gpr = s.gpr := m₆.gpr.trans g₅
  have w₆ : s₆.wr = s.wr := m₆.wr.trans w₅
  refine wp_str (a := slot H scr 6) (by have := ho 6 (by omega_nat); omega_nat) (ea g₆ 6 (by omega_nat))
    (io w₆ 6 (by omega_nat)) fun s₇ m₇ => ?_
  refine k s₇ (m₇.gpr.trans g₆) (by rw [m₇.rd, m₆.rd, m₅.rd, m₄.rd, m₃.rd, m₂.rd, m₁.rd])
    (m₇.wr.trans w₆) (by rw [m₇.sp, m₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, m₁.sp]) ?_ ?_
  · rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    have c : ∀ i < 7, (saveR H scr).Contains (slot H scr i) (64 / 8) := fun i hi => by
      rw [slot, ← add_ofNat_add]; exact contains_offset (by omega_nat) (by omega_nat)
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 3 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 5 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 6 (by omega_nat)))
  · have d : ∀ i j, i < 7 → j < 7 → i ≠ j → Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ :=
      fun i j hi hj hij => slot_disj H scr hi hj hij hW
    rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, g₆, g₅, g₄, g₃, g₂, m₁.gpr]
    have w : ∀ i j, i < 7 → j < 7 → i ≠ j → ∀ (m : Mem) (v : BitVec 64),
        (m.writeW (slot H scr j) v).readW (slot H scr i) 64 = m.readW (slot H scr i) 64 :=
      fun i j hi hj hij m v => readW_writeW_ne _ _ (d i j hi hj hij)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w 0 6 (by omega_nat) (by omega_nat) (by omega_nat), w 0 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 0 4 (by omega_nat) (by omega_nat) (by omega_nat), w 0 3 (by omega_nat) (by omega_nat) (by omega_nat),
        w 0 2 (by omega_nat) (by omega_nat) (by omega_nat), w 0 1 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 1 6 (by omega_nat) (by omega_nat) (by omega_nat), w 1 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 1 4 (by omega_nat) (by omega_nat) (by omega_nat), w 1 3 (by omega_nat) (by omega_nat) (by omega_nat),
        w 1 2 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [w 2 6 (by omega_nat) (by omega_nat) (by omega_nat), w 2 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 2 4 (by omega_nat) (by omega_nat) (by omega_nat), w 2 3 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 3 6 (by omega_nat) (by omega_nat) (by omega_nat), w 3 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 3 4 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [w 4 6 (by omega_nat) (by omega_nat) (by omega_nat), w 4 5 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 5 6 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `x23` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h23 : s.gpr .x23 = scr) (hW : H.W ≤ 1024) {s₀ : State}
    (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 7, InRegions (t.rd ++ t.wr) (slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (slot_in H hsc hL hW hi)
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega_nat
  have ea : ∀ {t : State}, t.gpr .x23 = scr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x23 + BitVec.ofNat 64 o = slot H scr i := fun h o i ho => by rw [h, ho]
  simp only [Hash.restore, Hash.saved, List.map_cons, List.map_nil]
  refine wp_ldr (a := slot H scr 0) (by have := ho 0 (by omega_nat); omega_nat) (ea h23 0 (by omega_nat))
    (io rfl rfl 0 (by omega_nat)) fun s₁ u₁ => ?_
  refine wp_ldr (a := slot H scr 1) (by have := ho 1 (by omega_nat); omega_nat)
    (ea (by rw [u₁.other _ (by decide), h23]) 1 (by omega_nat)) (io u₁.rd u₁.wr 1 (by omega_nat)) fun s₂ u₂ => ?_
  refine wp_ldr (a := slot H scr 2) (by have := ho 2 (by omega_nat); omega_nat)
    (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h23]) 2 (by omega_nat))
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega_nat)) fun s₃ u₃ => ?_
  refine wp_ldr (a := slot H scr 3) (by have := ho 3 (by omega_nat); omega_nat)
    (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]) 3 (by omega_nat))
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega_nat)) fun s₄ u₄ => ?_
  have r₄ : s₄.rd = s.rd := u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))
  have w₄ : s₄.wr = s.wr := u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))
  have x₄ : s₄.gpr .x23 = scr := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]
  refine wp_ldr (a := slot H scr 4) (by have := ho 4 (by omega_nat); omega_nat) (ea x₄ 4 (by omega_nat))
    (io r₄ w₄ 4 (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_ldr (a := slot H scr 5) (by have := ho 5 (by omega_nat); omega_nat)
    (ea (by rw [u₅.other _ (by decide), x₄]) 5 (by omega_nat)) (io (u₅.rd.trans r₄) (u₅.wr.trans w₄) 5 (by omega_nat))
    fun s₆ u₆ => ?_
  refine wp_ldr (a := slot H scr 6) (by have := ho 6 (by omega_nat); omega_nat)
    (ea (by rw [u₆.other _ (by decide), u₅.other _ (by decide), x₄]) 6 (by omega_nat))
    (io (u₆.rd.trans (u₅.rd.trans r₄)) (u₆.wr.trans (u₅.wr.trans w₄)) 6 (by omega_nat)) fun s₇ u₇ => ?_
  refine WP.block_nil ⟨by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, r₄], by rw [u₇.wr, u₆.wr, u₅.wr, w₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, fun r hr => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs.x19]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, hs.x20]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.mem, u₁.mem, hs.x21]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
        u₁.mem, hs.x22]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x24]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x30]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x23]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    rw [u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2,
      u₁.other r h1]

end VG.Proof.Hmac.Generic.AArch64

/-!
# HMAC over any streaming hash function on AArch64: `init`, correct

As on x86-64 (`Proof/Hmac/Generic/X86_64/Init.lean`). The return address is in
`x30`, which each call replaces: it is saved in `scratch` with our caller's
registers, and loaded back at the end. The other callee-saved registers we do
not use (`x25`–`x28`) are kept by the calls, and never written.
-/

namespace VG.Proof.Hmac.Generic.AArch64.Init

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt sub_offset contains_offset Upd wp_mov wp_movz wp_addImm)
open VG.Proof.Hmac.Generic.Common (add_ofNat_add bytesAt_prefix_congr inRegions_of_sub K0 K0_length
  BufMem off_disj off_disj0 covers_one sub_of_off sub_of_self bytes_keep take_map_xor)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev kp : Addr := s₀.gpr .x2
abbrev kl : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev stkR : Region := below s₀.sp 16
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
  sp16 : 16 ≤ s₀.sp.toNat
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
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hfit, hH.hBB, hH.hW, hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega_nat)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; simp only [Hash.buf] at this; exact sub_sc hp (by omega_nat) (by omega_nat)

theorem buf_sub : Region.Sub (bufR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hB; have := hp.hW
  exact sub_offset hp.fits (by simp only [Hash.buf] at *; omega_nat)

omit hp in
theorem padI_sub : Region.Sub ⟨P (H := H) s₀, H.B⟩ (bufR (H := H) s₀) := Region.sub_prefix (by omega_nat)

theorem padO_sub : Region.Sub ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (bufR (H := H) s₀) :=
  sub_offset (by omega_nat) (by have := hp.hB; omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 56) (by omega_nat) (by omega_nat)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 56) (n := 2 * H.B) (by omega_nat) (by omega_nat)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 56) (b := 8 * H.W + 56) (n := 2 * H.B) (by omega_nat) (by omega_nat)
    (by omega_nat)

end

/-! ## What the calls keep -/

/-- The callee-saved registers we never write. -/
abbrev untouched : List Reg := [.x25, .x26, .x27, .x28]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x20 : s.gpr .x20 = out s₀
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x23, .x25, .x26, .x27, .x28]

theorem untouched_kregs : ∀ r ∈ untouched, r ∈ kregs := by decide
theorem untouched_clob : ∀ r ∈ untouched, r ∉ clob := by decide
theorem untouched_pro : ∀ r ∈ untouched, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x14, .x15, .x24] := by
  decide

/-- `KR` survives changes to other registers, and to memory away from the
save area. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (untouched_kregs r hr)).trans (h.cs r hr),
    h.saved.frame H hf hs⟩

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

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
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega_nat
  have hB := hp.hB
  have hW := hp.hW
  refine WP.seq (save_ok H (scr := scr s₀) rfl (Nat.le_trans hp.hW (by decide)) hsc hL fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_movz fun s₇ u₇ => wp_movz fun s₈ u₈ => wp_movz fun s₉ u₉ => WP.block_nil ?_
  have k₉ : ∀ r, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x14, .x15, .x24] → s₉.gpr r = s₀.gpr r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
      rw [u₉.other r h8, u₈.other r h7, u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3,
        u₃.other r h2, u₂.other r h1, g₁]
  have e : ∀ r, s₉.gpr r = s₆.gpr r ∨ r ∈ [Reg.x14, .x15, .x24] := fun r => by
    by_cases h : r ∈ [Reg.x14, .x15, .x24]
    · exact .inr h
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      exact .inl (by rw [u₉.other r h.2.2, u₈.other r h.2.1, u₇.other r h.1])
  have e₆ : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s₉.gpr r = s₆.gpr r := fun r hr => by
    rcases e r with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h | h <;> cases h
  have h19 : s₉.gpr .x19 = inn s₀ := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have h20 : s₉.gpr .x20 = out s₀ := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  have h21 : s₉.gpr .x21 = kp s₀ := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h22 : s₉.gpr .x22 = s₀.gpr .x3 := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h23 : s₉.gpr .x23 = scr s₀ := by
    rw [e₆ _ (by simp), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h14 : s₉.gpr .x14 = (0x36 : BitVec 16).setWidth 64 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  have h15 : s₉.gpr .x15 = (0x5c : BitVec 16).setWidth 64 := by
    rw [u₉.other _ (by decide), u₈.gpr]
  have h24 : s₉.gpr .x24 = BitVec.ofNat 64 0 := by rw [u₉.gpr]; rfl
  have hm₉ : s₉.mem = s₁.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hrd : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have hwr : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have hsp : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  have hr : LoopRegs H (P (H := H) s₀) (kp s₀) (kl s₀) s₉ :=
    ⟨by rw [h23], h21, by rw [h22, BitVec.ofNat_toNat, BitVec.setWidth_eq], h14, h15⟩
  have hm : LoopMem H (P (H := H) s₀) (kp s₀) (kl s₀) s₉ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (s₀.gpr .x3).isLt hk |>.elim
          fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega_nat) hk,
      hp.k_s.sub_right (buf_sub hp), hB, by simp only [Hash.buf]; omega_nat⟩
  refine WP.seq (WP.mono (key_ok H hr hm h24) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₉.mem := hm₉ ▸ f₁
  have eK : K0 s₉.mem (kp s₀) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp))) (by
      exact Nat.le_of_lt (s₀.gpr .x3).isLt) hi
  have hg : ∀ r ∉ clob, t.gpr r = s₉.gpr r := ht.other
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [ht.sp, hsp],
    by rw [hg _ (by decide), h19], by rw [hg _ (by decide), h20], by rw [hg _ (by decide), h23],
    fun r hr => by rw [hg r (untouched_clob r hr), k₉ r (untouched_pro r hr)],
    sv₁.frame H (hm₉ ▸ ht.mem.frame) (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp)⟩,
    ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem state_disj {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p, H.S⟩ := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.stk_i⟩
  · exact ⟨hp.o_s, hp.stk_o⟩

theorem state_in {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨p, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem kr_mov {s t : State} (hk : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s t d v) : KR (H := H) s₀ t :=
  hk.keep u.rd u.wr u.sp (fun r hr => u.other r fun h => hd (h ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

omit hp in
theorem initArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p) :
    WP isa (.block [VG.Impl.Sha256.AArch64.Stream.mov .x0 st]) s
      fun t => KR (H := H) s₀ t ∧ t.gpr .x0 = p ∧ t.mem = s.mem :=
  wp_mov fun s₁ u₁ => WP.block_nil ⟨kr_mov hk (by decide) u₁, by rw [u₁.gpr, hs], u₁.mem⟩

/-- `KR` after a call that writes `rs`. -/
theorem kr_after {t s' : State} (hk : KR (H := H) s₀ t) {rs : List Region} (ha : After t rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [hk.sp] at f
  refine hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f ?_
  simp only [List.mem_append, List.mem_singleton]
  rintro r (hr | rfl)
  · exact hs r hr
  · exact hp.stk_s.symm.sub_left (save_sub hp)

theorem initCall_ok {t : State} (hk : KR (H := H) s₀ t) {p : Addr} (hd : t.gpr .x0 = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', VecKept t s' → KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] t.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (.call H.initN H.initC) t Q := by
  obtain ⟨dS, _⟩ := state_disj hp hpR
  refine init_call hH hd (by rw [hk.wr]; exact covers_one (state_in hp hpR)) fun s' ha hr => ?_
  have f := ha.frame
  rw [hk.sp] at f
  exact hQ s' ha.vec (kr_after hp hk ha (by
    simp only [List.mem_singleton]; rintro r rfl; exact dS.symm.sub_left (save_sub hp))) f hr

theorem callInit_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', VecKept s s' → KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.callInit st) s Q :=
  WP.seq (WP.mono (WP.preservedV (initArgs_ok hk hs) (by rfl)) fun _ ⟨⟨k, d, m⟩, hv⟩ =>
    initCall_ok hH hp k d hpR fun s' hv' k' f r => hQ s' (VecKept.trans hv hv') k' (m ▸ f) r)

/-- The arguments of `init`'s calls of `update`. -/
abbrev dO (s₀ : State) (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block ([VG.Impl.Sha256.AArch64.Stream.mov .x0 st] ++
        ([.movz .x .x1 (BitVec.ofNat 16 0) 0, .addImm .x .x2 .x23 o, .movz .x .x3 (BitVec.ofNat 16 H.B) 0,
          VG.Impl.Sha256.AArch64.Stream.mov .x4 .x23] : List Instr))) s fun t =>
      KR (H := H) s₀ t ∧ UpdArgs hH t p (dO s₀ o) (scr s₀) H.B ∧ t.gpr .x1 = 0 ∧ t.mem = s.mem := by
  obtain ⟨dS, dK⟩ := state_disj hp hpR
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o < 4096 := by omega_nat
  have dsub : Region.Sub ⟨dO s₀ o, H.B⟩ (bufR (H := H) s₀) := by
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [dO, ← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨dO s₀ o, H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_addImm ho' fun s₃ u₃ => wp_movz fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ : KR (H := H) s₀ s₅ :=
    kr_mov (kr_mov (kr_mov (kr_mov (kr_mov hk (by decide) u₁) (by decide) u₂) (by decide) u₃)
      (by decide) u₄) (by decide) u₅
  have h23 : s.gpr .x23 = scr s₀ := hk.x23
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
    hm⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, hs]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h23]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, movz_ofNat (by omega_nat), toNat_ofNat_lt (by omega_nat)]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h23]
      cd := by
        rw [k₅.rd, k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.wr]; simp) (by omega_nat)
      cw := by
        rw [k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨p, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega_nat)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      sp16 := by rw [k₅.sp]; exact hp.sp16
      stk_st := by rw [k₅.sp]; exact dK
      stk_d := by rw [k₅.sp]; exact hp.stk_s.sub_right dsc
      stk_sc := by rw [k₅.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) {p d : Addr} (hpR : p = inn s₀ ∨ p = out s₀)
    (ha : UpdArgs hH t p d (scr s₀) H.B) (hx1 : t.gpr .x1 = 0) {Q : State → Prop}
    (hQ : ∀ s', VecKept t s' → KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt t.mem d H.B)) → Q s') :
    WP isa (.call H.updN H.updC) t Q := by
  obtain ⟨dS, _⟩ := state_disj hp hpR
  refine upd_call hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.sp] at f
  refine hQ s' ha'.vec (kr_after hp hk ha' ?_) f fun hr => hpost [] hr (by rw [hx1]; rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact dS.symm.sub_left (save_sub hp)
  · exact (cal_save hH hp).symm

theorem callUpd_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', VecKept s s' → KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt s.mem (scr s₀ + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [VG.Impl.Sha256.AArch64.Stream.mov .x0 st] 0 o H.B) s Q :=
  WP.seq (WP.mono (WP.preservedV (updArgs_ok hH hp hk hs hpR ho) (by rfl)) fun _ ⟨⟨k, a, x1, m⟩, hv⟩ =>
    updCall_ok hH hp k hpR a x1 fun s' hv' k' f r => hQ s' (VecKept.trans hv hv') k' (m ▸ f) (m ▸ r))

/-! ## Correctness -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.Common.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega_nat,
    ↓reduceIte]

omit hp in
/-- The end: `abiPreserved`, from `KR` and `restore`. -/
theorem abi_of {s s' : State} (hk : KR (H := H) s₀ s) (hsp : s'.sp = s.sp) (hv : VecKept s₀ s')
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) (ho : ∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, by rw [hsp, hk.sp], hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hg _ (by decide)
    | exact (ho _ (by decide)).trans (hk.cs _ (by decide))

theorem correct :
    WP isa H.init s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
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
  refine WP.seq (WP.mono (WP.preservedV (keys_ok sc hp) (by rfl)) fun s₁ ⟨h₁, hv₁⟩ => ?_)
  refine WP.seq (callInit_ok hH hp h₁.kr (st := .x19) h₁.kr.x19 (.inl rfl) fun s₂ hv₂ k₂ f₂ r₂ => ?_)
  have bI₂ := (bytes_keep f₂ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans h₁.bufI
  have bO₂ := (bytes_keep f₂ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans h₁.bufO
  refine WP.seq (callUpd_ok hH hp k₂ k₂.x19 (.inl rfl) (.inl rfl) fun s₃ hv₃ k₃ f₃ r₃ => ?_)
  have rI₃ := r₃ r₂
  rw [List.nil_append, bI₂] at rI₃
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans bO₂
  refine WP.seq (callInit_ok hH hp k₃ (st := .x20) k₃.x20 (.inr rfl) fun s₄ hv₄ k₄ f₄ r₄ => ?_)
  have rI₄ := repr_keep hH f₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.stk_i.symm) rI₃
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans bO₃
  refine WP.seq (callUpd_ok hH hp k₄ k₄.x20 (.inr rfl) (.inr rfl) fun s₅ hv₅ k₅ f₅ r₅ => ?_)
  have rO₅ := r₅ r₄
  rw [List.nil_append, eO, bO₄] at rO₅
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.stk_i.symm) rI₄
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₅.wr := by rw [k₅.wr, hp.wr]; simp
  refine WP.mono (WP.preservedV (restore_ok H k₅.x23 (Nat.le_trans hW (by decide)) k₅.saved hsc (by omega_nat)) (by rfl)) fun s' ⟨⟨hm, _, _, hsp, hg, ho⟩, hv₆⟩ => ?_
  refine ⟨abi_of k₅ hsp (fun r hr => (hv₆ r hr).trans ((hv₅ r hr).trans ((hv₄ r hr).trans ((hv₃ r hr).trans ((hv₂ r hr).trans (hv₁ r hr)))))) hg ho, ?_⟩
  show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨rI₅, rO₅⟩

end

end VG.Proof.Hmac.Generic.AArch64.Init
