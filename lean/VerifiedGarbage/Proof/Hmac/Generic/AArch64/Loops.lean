import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Loops
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common

/-!
# HMAC over any streaming hash function on AArch64: the byte loops

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Loops.lean`, whose lemmas on byte lists and
memory are reused): the byte copy (`copy`), used for states, digests and
`U`; the exclusive-or of `U` into `T`; and `init`'s loops that write
`K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each counts `x24` up from 0, and computes the
bytes left into `x11`, on which it branches.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy left)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeW8_apply)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt)
open VG.Proof.Sha256.AArch64.Stream (Upd Mupd wp_add wp_sub wp_addImm wp_movz wp_ldrb wp_strb
  eval_nonzero eval_zero ofNat_succ)
open VG.Proof.Hmac.X86_64 (bytesAt_length)
open VG.Proof.Hmac.Generic.X86_64 (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint add_ofNat_ne
  add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge xorBytes_snoc xorBytes_length'
  InRegions.right')
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.Sha256.AArch64.Stream.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Proof.Sha256.AArch64.Stream.Upd.write64 _ _ _))

end

theorem movz_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_ne_zero {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = decide (a ≠ 0) := by
  by_cases ha : a = 0
  · subst ha; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => ha (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this)
    rw [show (BitVec.ofNat 64 a != 0) = true from bne_iff_ne.mpr this]; simp [ha]

/-- `x11` after `movz x11, n; sub x11, x11, x24` with `x24 = k ≤ n`. -/
theorem left_val {n k : Nat} (hk : k ≤ n) (hn : n < 2 ^ 16) :
    (BitVec.ofNat 16 n).setWidth 64 - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  rw [movz_ofNat hn, sub_ofNat' hk (by omega)]

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
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' h' => ?_
  obtain ⟨hi', hx⟩ := h'
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (n - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, hx, ofNat_ne_zero (by omega)]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp; omega, n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

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
  refine WP.mono (count_loop hn (by omega) (CopyInv s A B) (fun k hk t h => ?_) i0)
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
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega)
    rw [hl] at e'
    rw [u₇.mem, u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), h24, left_val (by omega) hn']

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
      (.loop (.block ([.add .x .x12 .x23 .x24, .ldrb .x9 .x12 uo, .add .x .x13 .x20 .x24,
        .ldrb .x10 .x13 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x13 0, .addImm .x .x24 .x24 1] ++
        left n)) (.nonzero .x .x11))) s
      fun t => XorInv s (s.gpr .x23 + BitVec.ofNat 64 uo) (s.gpr .x20) n t := by
  set U := s.gpr .x23 + BitVec.ofNat 64 uo
  set T := s.gpr .x20
  refine WP.seq (wp_movz fun s₀ u₀ => WP.block_nil ?_)
  have i0 : XorInv s U T 0 s₀ :=
    ⟨u₀.rd, u₀.wr, u₀.sp, fun r hr => u₀.other r (nm hr .x24), by rw [u₀.gpr]; rfl,
      by rw [u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil]⟩
  refine count_loop hn (by omega) (XorInv s U T) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (le_of_lt hk) (by omega), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by bv_omega,
      toNat_ofNat_lt (show k < 2 ^ 64 by omega), Nat.lt_irrefl, ↓reduceIte]
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
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega)
    rw [hl'] at e'
    rw [u₉.mem, u₈.mem, u₇.mem, m₆.mem, hv, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem, e',
      bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), h24, left_val (by omega) hn']

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
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep H h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.Sha256.X86_64.contains_offset (n := 1) (by omega) (by omega)) hc
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
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega)
    (by rw [u₄.other _ (by decide), a12, rt.x23])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₅ m₅ => ?_
  refine wp_eor fun t₆ u₆ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), a12, ← add_ofNat_add, rt.x23])
    (by rw [u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega))
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
    exact buf_write h.mem hB (by omega) hl
  · rw [u₉.gpr, u₈.other _ (by decide), h24, m₇.gpr, u₆.other _ (by decide), m₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      rt.x22, sub_ofNat' (by omega) (by omega)]

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
    rw [eval_zero, hr.x22, Proof.Sha256.AArch64.Stream.ofNat_beq_zero (by omega)]
  refine WP.ite (decide (kl = 0)) hz (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (by omega) (KeyInv H s P K kl) (fun j hj t h => key_step H hr hm hj h) i0

theorem pad_step {P K : Addr} {kl : Nat} {s₀ : State} (hr : LoopRegs H P K kl s₀) (hm : LoopMem H P K kl s₀)
    {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {t : State} (h : KeyInv H s₀ P K kl j t) :
    WP isa (.block ([.add .x .x12 .x23 .x24, .strb .x14 .x12 H.buf, .strb .x15 .x12 (H.buf + H.B),
      .addImm .x .x24 .x24 1] ++ left H.B)) t
      fun t' => KeyInv H s₀ P K kl (j + 1) t' ∧ t'.gpr .x11 = BitVec.ofNat 64 (H.B - (j + 1)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hbuf := hm.hbuf
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep H h.other
  refine wp_add fun t₁ u₁ => ?_
  have a12 : ∀ o, t₁.gpr .x12 + BitVec.ofNat 64 o = t.gpr .x23 + BitVec.ofNat 64 o + BitVec.ofNat 64 j :=
    fun o => by rw [u₁.gpr, h.x24]; ac_rfl
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega) (by rw [a12, rt.x23])
    (by rw [u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₂ m₂ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [m₂.gpr, a12, ← add_ofNat_add, rt.x23])
    (by rw [m₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega)) fun t₃ m₃ => ?_
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
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), h24, left_val (by omega) (by omega)]

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
    rw [eval_zero, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.x24, left_val hkl (by omega),
      Proof.Sha256.AArch64.Stream.ofNat_beq_zero (by omega)]
    congr 1; exact decide_eq_decide.mpr (by omega)
  refine WP.ite (decide (kl = H.B)) hz (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0
  · have : kl < H.B := by simp at h0; omega
    have := count_loop (n := H.B - kl) (by omega) (by omega) (fun k t => KeyInv H s₀ P K kl (kl + k) t)
      (fun k hk t hk' => WP.mono (pad_step H hr hm (j := kl + k) (by omega) (by omega) hk')
        fun t' ⟨a, b⟩ => ⟨by rw [← Nat.add_assoc]; exact a, by rw [b]; congr 1; omega⟩)
      (s := t₂) (by simpa using i0)
    rw [show kl + (H.B - kl) = H.B by omega] at this
    exact this

end VG.Proof.Hmac.Generic.AArch64
