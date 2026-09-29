import VerifiedGarbage.Proof.Hmac.Generic.Arm.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# HMAC over any streaming hash function on 32-bit ARM: the byte loops

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/Loops.lean`, with the byte-list lemmas of
`Proof/Hmac/Generic/Common.lean`): the byte copy (`copy`), the exclusive-or
of `U` into `T`, and `init`'s loops that write `K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each counts `r8` up
from 0 and `r9` down to 0 with `subs`, and branches on its result.
Addresses are 32 bits, zero-extended: every buffer the loops touch lies
below 2³², so byte `k` of a buffer at `p + o` is at `State.addr p + o + k`.
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd WP.cons op2_imm op2_reg wp_mov wp_add wp_subs wp_ldrb wp_strb
  eval_ne sub_beq sub_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint xorBytes_snoc xorBytes_length'
  InRegions.right' add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem ofNat_succ32 (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem movw_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Byte `k` of the buffer at `a + o`, as a loop addresses it. -/
theorem addr3 {a : BitVec 32} {k o : Nat} (h : a.toNat + o + k < 2 ^ 32) :
    State.addr (a + BitVec.ofNat 32 k + BitVec.ofNat 32 o) = State.addr a + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), BitVec.ofNat_add, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 k)]

/-- The flags after counting `r9` down from `n - k` to `n - (k + 1)`. -/
theorem left_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (n - (k + 1) = 0) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
  simp only [decide_eq_decide]; omega

theorem left_val {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]

/-- The registers the loops write. -/
abbrev clob : List Reg := [.r1, .r2, .r8, .r9, .r12]

/-- The registers `copy` writes. -/
abbrev cclob : List Reg := [.r2, .r8, .r9, .r12]

theorem not_cclob {r : Reg} (h : r ∉ clob) : r ∉ cclob := fun hc =>
  h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; tauto)

theorem nm {r : Reg} {l : List Reg} (h : r ∉ l) (x : Reg) (hx : x ∈ l := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `ne` that runs its body `n > 0` times, each run
ending with the flags of `n - (k + 1) = 0`. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧ s'.z = decide (n - (k + 1) = 0))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (n - (k + 1) = 0)) := by
    show eval .ne s' = _; rw [eval_ne, hz]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp; omega, n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copy` -/

/-- After `k` bytes of a `copy` of `n` bytes from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  r8 : t.gpr .r8 = BitVec.ofNat 32 k
  r9 : t.gpr .r9 = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ∉ cclob) (hd : dst ∉ cclob)
    {so d n : Nat} (hso : so < 4096) (hdo : d < 4096) (hn : 0 < n) (hn' : n < 2 ^ 16) {s : State}
    (hsw : (s.gpr src).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr dst).toNat + d + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, n⟩
      ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      Copied s (State.addr (s.gpr dst) + BitVec.ofNat 64 d)
        (bytesAt s.mem (State.addr (s.gpr src) + BitVec.ofNat 64 so) n) t := by
  set A := State.addr (s.gpr src) + BitVec.ofNat 64 so
  set B := State.addr (s.gpr dst) + BitVec.ofNat 64 d
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => VG.Proof.Hmac.Generic.Arm.wp_movw fun s₁ u₁ =>
    WP.block_nil ?_)
  have i0 : CopyInv s A B n 0 s₁ :=
    ⟨by rw [u₁.rd, u₀.rd], by rw [u₁.wr, u₀.wr], by rw [u₁.sp, u₀.sp],
      fun r hr => by rw [u₁.other r (nm hr .r9), u₀.other r (nm hr .r8)],
      by rw [u₁.other _ (by decide), u₀.gpr]; rfl, by rw [u₁.gpr, movw_ofNat hn']; rfl,
      by rw [u₁.mem, u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (count_loop hn (CopyInv s A B n) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.sp, h.other, h.mem⟩
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := A + BitVec.ofNat 64 k) hso
    (by rw [u₁.gpr, h.other src hs, h.r8, addr3 (by omega)])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) hdo
    (by rw [u₃.gpr, u₂.other dst (nm hd .r12), u₁.other dst (nm hd .r2), h.other dst hd,
      u₂.other .r8 (by decide), u₁.other .r8 (by decide), h.r8, addr3 (by omega)])
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₄ m₄ => ?_
  refine wp_add (op2_imm (by decide)) fun t₅ u₅ => wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ =>
    WP.block_nil ?_
  have h8 : t₅.gpr .r8 = BitVec.ofNat 32 (k + 1) := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8,
      ofNat_succ32]
  have h9 : t₅.gpr .r9 = BitVec.ofNat 32 (n - k) := by
    rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, m₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, m₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₆.sp, u₅.sp, m₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₆.other r (nm hr .r9), u₅.other r (nm hr .r8), m₄.gpr, u₃.other r (nm hr .r2), u₂.other r (nm hr .r12),
        u₁.other r (nm hr .r2), h.other r hr],
    by rw [u₆.other _ (by decide), h8], by rw [u₆.gpr, h9, left_val hk], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₃.gpr .r12).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.mem]
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega)
    rw [hl] at e'
    rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [z₆, h9, left_z hk (by omega)]

/-! ## The exclusive-or of `U` into `T` -/

theorem xor_byte32 (a b : Byte) : ((b.setWidth 32 ^^^ a.setWidth 32).setWidth 8) = b ^^^ a := by
  ext i hi
  simp [BitVec.getElem_xor]

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  r8 : t.gpr .r8 = BitVec.ofNat 32 k
  r9 : t.gpr .r9 = BitVec.ofNat 32 (n - k)
  mem : t.mem = writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `r11 + uo` and `T` at `r5`. -/
theorem xor_ok {uo n : Nat} (huo : uo < 4096) (hn : 0 < n) (hn' : n < 2 ^ 16) {s : State}
    (huw : (s.gpr .r11).toNat + uo + n ≤ 2 ^ 32) (htw : (s.gpr .r5).toNat + n ≤ 2 ^ 32)
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r11) + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr (State.addr (s.gpr .r5) + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r11) + BitVec.ofNat 64 uo, n⟩ ⟨State.addr (s.gpr .r5), n⟩) :
    WP isa (.seq (.block [.mov .r8 (.imm 0), .movw .r9 (BitVec.ofNat 16 n)])
      (.loop (.block [.dp .add .r2 .r11 (.reg .r8), .ldrb .r12 .r2 uo, .dp .add .r2 .r5 (.reg .r8),
        .ldrb .r1 .r2 0, .dp .eor .r1 .r1 (.reg .r12), .strb .r1 .r2 0, .dp .add .r8 .r8 (.imm 1),
        .subs .r9 .r9 (.imm 1)]) .ne)) s
      fun t => XorInv s (State.addr (s.gpr .r11) + BitVec.ofNat 64 uo) (State.addr (s.gpr .r5)) n n t := by
  set U := State.addr (s.gpr .r11) + BitVec.ofNat 64 uo
  set T := State.addr (s.gpr .r5)
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => VG.Proof.Hmac.Generic.Arm.wp_movw fun s₁ u₁ =>
    WP.block_nil ?_)
  have i0 : XorInv s U T n 0 s₁ :=
    ⟨by rw [u₁.rd, u₀.rd], by rw [u₁.wr, u₀.wr], by rw [u₁.sp, u₀.sp],
      fun r hr => by rw [u₁.other r (nm hr .r9), u₀.other r (nm hr .r8)],
      by rw [u₁.other _ (by decide), u₀.gpr]; rfl, by rw [u₁.gpr, movw_ofNat hn']; rfl,
      by rw [u₁.mem, u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil]⟩
  refine count_loop hn (XorInv s U T n) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.lt_irrefl, ↓reduceIte]
  have g11 := h.other .r11 (by decide)
  have g5 := h.other .r5 (by decide)
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := U + BitVec.ofNat 64 k) huo (by rw [u₁.gpr, g11, h.r8, addr3 (by omega)])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  have a₃ : State.addr (t₃.gpr .r2 + BitVec.ofNat 32 0) = T + BitVec.ofNat 64 k := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g5, h.r8, addr3 (by omega)]
    exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _)
  refine wp_ldrb (a := T + BitVec.ofNat 64 k) (by decide) a₃
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact InRegions.right' (houtT k hk))
    fun t₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun t₅ u₅ => ?_
  refine wp_strb (a := T + BitVec.ofNat 64 k) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact a₃)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact houtT k hk) fun t₆ m₆ => ?_
  refine wp_add (op2_imm (by decide)) fun t₇ u₇ => wp_subs (op2_imm (by decide)) fun t₈ u₈ z₈ =>
    WP.block_nil ?_
  have h8 : t₇.gpr .r8 = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r8, ofNat_succ32]
  have h9 : t₇.gpr .r9 = BitVec.ofNat 32 (n - k) := by
    rw [u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r9]
  refine ⟨⟨by rw [u₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₈.sp, u₇.sp, m₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr => by
      rw [u₈.other r (nm hr .r9), u₇.other r (nm hr .r8), m₆.gpr, u₅.other r (nm hr .r1), u₄.other r (nm hr .r1),
        u₃.other r (nm hr .r2), u₂.other r (nm hr .r12), u₁.other r (nm hr .r2), h.other r hr],
    by rw [u₈.other _ (by decide), h8], by rw [u₈.gpr, h9, left_val hk], ?_⟩, ?_⟩
  · have hv : (t₅.gpr .r1).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
      rw [u₅.gpr, u₄.gpr, u₄.other .r12 (by decide), u₃.other .r12 (by decide), u₂.gpr, u₃.mem, u₂.mem,
        u₁.mem, xor_byte32, rU, rT]
    have e' := writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega)
    rw [hl'] at e'
    rw [u₈.mem, u₇.mem, m₆.mem, hv, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem, e',
      bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [z₈, h9, left_z hk (by omega)]

/-! ## `init`'s key and pad loops

`K₀ ⊕ ipad` is written at `P = scratch + buf` and `K₀ ⊕ opad` at `P + B`,
byte by byte (as on x86-64, `BufMem`): first the key's `kl` bytes (read at
`K`), then the zeros that pad it to `B`. -/

variable (H : Hash)

/-- Where the loops are. -/
structure LoopRegs (scr kp : BitVec 32) (s : State) : Prop where
  r11 : s.gpr .r11 = scr
  r6 : s.gpr .r6 = kp

theorem LoopRegs.keep {scr kp : BitVec 32} {s t : State} (h : LoopRegs scr kp s)
    (hk : ∀ r ∉ clob, t.gpr r = s.gpr r) : LoopRegs scr kp t :=
  ⟨by rw [hk _ (by decide), h.r11], by rw [hk _ (by decide), h.r6]⟩

/-- The loops' invariant, from the state `s` they start in. -/
structure KeyInv (s : State) (P K : Addr) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  r8 : t.gpr .r8 = BitVec.ofNat 32 j
  mem : BufMem H.B P (K0 s.mem K kl H.B) s.mem j t.mem

/-- The regions the loops access, and the sizes. -/
structure LoopMem (scr kp : BitVec 32) (kl : Nat) (s : State) : Prop where
  kl_le : kl ≤ H.B
  key : ∀ k < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 k) 1
  buf : ∀ k < 2 * H.B, InRegions s.wr (State.addr scr + BitVec.ofNat 64 H.buf + BitVec.ofNat 64 k) 1
  disj : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr scr + BitVec.ofNat 64 H.buf, 2 * H.B⟩
  hB : H.B ≤ 128
  hbuf : H.buf + H.B < 4096
  nscr : scr.toNat + H.buf + 2 * H.B ≤ 2 ^ 32
  nkey : kp.toNat + kl ≤ 2 ^ 32

/-- The bodies of `init`'s loops. -/
def keyBody : List Instr :=
  [.dp .add .r2 .r6 (.reg .r8), .ldrb .r12 .r2 0, .dp .eor .r1 .r12 (.imm 0x36),
    .dp .add .r2 .r11 (.reg .r8), .strb .r1 .r2 H.buf, .dp .eor .r1 .r12 (.imm 0x5c),
    .strb .r1 .r2 (H.buf + H.B), .dp .add .r8 .r8 (.imm 1), .subs .r9 .r9 (.imm 1)]

def padBody : List Instr :=
  [.dp .add .r2 .r11 (.reg .r8), .mov .r1 (.imm 0x36), .strb .r1 .r2 H.buf,
    .mov .r1 (.imm 0x5c), .strb .r1 .r2 (H.buf + H.B), .dp .add .r8 .r8 (.imm 1),
    .subs .r9 .r9 (.imm 1)]

theorem keyLoop_eq : H.keyLoop = .loop (.block (keyBody H)) .ne := rfl
theorem padLoop_eq : H.padLoop = .loop (.block (padBody H)) .ne := rfl

theorem pad_byte32 (b : Byte) (v : BitVec 32) : (b.setWidth 32 ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem ipad32 : (0x36 : BitVec 32).setWidth 8 = Spec.Hmac.ipad := by decide
theorem opad32 : (0x5c : BitVec 32).setWidth 8 = Spec.Hmac.opad := by decide
theorem zero_ipad : (0x36 : BitVec 32).setWidth 8 = (0 : Byte) ^^^ Spec.Hmac.ipad := by decide
theorem zero_opad : (0x5c : BitVec 32).setWidth 8 = (0 : Byte) ^^^ Spec.Hmac.opad := by decide

theorem key_step {scr kp : BitVec 32} {kl : Nat} {s : State} (hr : LoopRegs scr kp s)
    (hm : LoopMem H scr kp kl s) {j : Nat} (hj : j < kl) {t : State}
    (h : KeyInv H s (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl j t)
    (h9 : t.gpr .r9 = BitVec.ofNat 32 (kl - j)) :
    WP isa (.block (keyBody H)) t fun t' => (KeyInv H s (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl (j + 1) t' ∧
      t'.gpr .r9 = BitVec.ofNat 32 (kl - (j + 1))) ∧ t'.z = decide (kl - (j + 1) = 0) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hbuf := hm.hbuf
  have hn := hm.nscr
  have hnk := hm.nkey
  set P := State.addr scr + BitVec.ofNat 64 H.buf
  set K := State.addr kp
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.MdStream.Arm.contains_offset (n := 1) (by omega) (by omega)) hc
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.gpr, rt.r6, h.r8, addr3 (by omega)]; exact congrArg (· + BitVec.ofNat 64 j) (BitVec.add_zero _))
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hm.key j hj) fun t₂ u₂ => ?_
  refine wp_eor (op2_imm (by decide)) fun t₃ u₃ => ?_
  refine wp_add (op2_reg _ _) fun t₄ u₄ => ?_
  have a4 : ∀ o, o + j < 2 ^ 32 - scr.toNat → State.addr (t₄.gpr .r2 + BitVec.ofNat 32 o) =
      State.addr scr + BitVec.ofNat 64 o + BitVec.ofNat 64 j := fun o ho => by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), rt.r11,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8, addr3 (by omega)]
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega) (a4 _ (by omega))
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₅ m₅ => ?_
  refine wp_eor (op2_imm (by decide)) fun t₆ u₆ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [u₆.other _ (by decide), m₅.gpr, a4 _ (by omega)]; simp only [P, add_ofNat_add])
    (by rw [u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega))
    fun t₇ m₇ => ?_
  refine wp_add (op2_imm (by decide)) fun t₈ u₈ => wp_subs (op2_imm (by decide)) fun t₉ u₉ z₉ =>
    WP.block_nil ?_
  have k : ∀ r ∉ clob, t₉.gpr r = t.gpr r := fun r hr' => by
    rw [u₉.other r (nm hr' .r9), u₈.other r (nm hr' .r8), m₇.gpr, u₆.other r (nm hr' .r1), m₅.gpr,
      u₄.other r (nm hr' .r2), u₃.other r (nm hr' .r1), u₂.other r (nm hr' .r12), u₁.other r (nm hr' .r2)]
  have h8 : t₈.gpr .r8 = BitVec.ofNat 32 (j + 1) := by
    rw [u₈.gpr, m₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r8, ofNat_succ32]
  have h9' : t₈.gpr .r9 = BitVec.ofNat 32 (kl - j) := by
    rw [u₈.other _ (by decide), m₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9]
  refine ⟨⟨⟨by rw [u₉.rd, u₈.rd, m₇.rd, u₆.rd, m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₉.wr, u₈.wr, m₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₉.sp, u₈.sp, m₇.sp, u₆.sp, m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr' => by rw [k r hr', h.other r hr'], by rw [u₉.other _ (by decide), h8], ?_⟩,
    by rw [u₉.gpr, h9', left_val hj]⟩, by rw [z₉, h9', left_z hj (by omega)]⟩
  have r12 : t₃.gpr .r12 = (t.mem (K + BitVec.ofNat 64 j)).setWidth 32 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
  have v₁ : (t₄.gpr .r1).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.ipad := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem, pad_byte32, hbyte, ipad32]
  have v₂ : (t₆.gpr .r1).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.opad := by
    rw [u₆.gpr, m₅.gpr, u₄.other .r12 (by decide), r12, pad_byte32, hbyte, opad32]
  rw [u₉.mem, u₈.mem, m₇.mem, v₂, u₆.mem, m₅.mem, v₁, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact buf_write h.mem hB (by omega) hl

theorem pad_step {scr kp : BitVec 32} {kl : Nat} {s₀ : State} (hr : LoopRegs scr kp s₀)
    (hm : LoopMem H scr kp kl s₀) {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {t : State}
    (h : KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl j t)
    (h9 : t.gpr .r9 = BitVec.ofNat 32 (H.B - j)) :
    WP isa (.block (padBody H)) t fun t' =>
      (KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl (j + 1) t' ∧
        t'.gpr .r9 = BitVec.ofNat 32 (H.B - (j + 1))) ∧ t'.z = decide (H.B - (j + 1) = 0) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hbuf := hm.hbuf
  have hn := hm.nscr
  set P := State.addr scr + BitVec.ofNat 64 H.buf
  set K := State.addr kp
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep h.other
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  have a1 : ∀ o, o + j < 2 ^ 32 - scr.toNat → State.addr (t₁.gpr .r2 + BitVec.ofNat 32 o) =
      State.addr scr + BitVec.ofNat 64 o + BitVec.ofNat 64 j := fun o ho => by
    rw [u₁.gpr, rt.r11, h.r8, addr3 (by omega)]
  refine wp_mov (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega) (by rw [u₂.other _ (by decide)]; exact a1 _ (by omega))
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₃ m₃ => ?_
  refine wp_mov (op2_imm (by decide)) fun t₄ u₄ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [u₄.other _ (by decide), m₃.gpr, u₂.other _ (by decide), a1 _ (by omega)]; simp only [P, add_ofNat_add])
    (by rw [u₄.wr, m₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega)) fun t₅ m₅ => ?_
  refine wp_add (op2_imm (by decide)) fun t₆ u₆ => wp_subs (op2_imm (by decide)) fun t₇ u₇ z₇ =>
    WP.block_nil ?_
  have h8 : t₆.gpr .r8 = BitVec.ofNat 32 (j + 1) := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r8,
      ofNat_succ32]
  have h9' : t₆.gpr .r9 = BitVec.ofNat 32 (H.B - j) := by
    rw [u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), m₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h9]
  refine ⟨⟨⟨by rw [u₇.rd, u₆.rd, m₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, m₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₇.sp, u₆.sp, m₅.sp, u₄.sp, m₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr' => by
      rw [u₇.other r (nm hr' .r9), u₆.other r (nm hr' .r8), m₅.gpr, u₄.other r (nm hr' .r1), m₃.gpr,
        u₂.other r (nm hr' .r1), u₁.other r (nm hr' .r2), h.other r hr'],
    by rw [u₇.other _ (by decide), h8], ?_⟩, by rw [u₇.gpr, h9', left_val hj']⟩,
    by rw [z₇, h9', left_z hj' (by omega)]⟩
  rw [u₇.mem, u₆.mem, m₅.mem, u₄.gpr, u₄.mem, m₃.mem, u₂.gpr, u₂.mem, u₁.mem, zero_ipad, zero_opad,
    ← K0_ge (m := s₀.mem) (K := K) (B := H.B) hj hl]
  exact buf_write h.mem hB hj' hl

/-- The key loop, skipped for an empty key: from `r8 = 0`, `r9 = kl` and the flags of `kl = 0`. -/
theorem key_ok {scr kp : BitVec 32} {kl : Nat} {s : State} (hr : LoopRegs scr kp s) (hm : LoopMem H scr kp kl s)
    (h8 : s.gpr .r8 = BitVec.ofNat 32 0) (h9 : s.gpr .r9 = BitVec.ofNat 32 kl) (hz : s.z = decide (kl = 0)) :
    WP isa (.ite .eq (.block []) H.keyLoop) s
      (KeyInv H s (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl kl) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have i0 : KeyInv H s (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, h8, ⟨by simp [bytesAt], by simp [bytesAt], Frame.refl _ _⟩⟩
  refine WP.ite (decide (kl = 0)) (by show eval .eq s = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have hpos : 0 < kl := by simp at h0; omega
    rw [keyLoop_eq]
    exact WP.mono (count_loop hpos (fun k t => KeyInv H s (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl k t ∧
        t.gpr .r9 = BitVec.ofNat 32 (kl - k))
      (fun k hk t ⟨h, h9'⟩ => key_step H hr hm hk h h9') ⟨i0, by rw [h9, Nat.sub_zero]⟩) fun _ h => h.1

/-- The pad loop, skipped for a key of `B` bytes: from `r8 = kl`. -/
theorem pad_ok {scr kp : BitVec 32} {kl : Nat} {s₀ : State} (hr : LoopRegs scr kp s₀) (hm : LoopMem H scr kp kl s₀)
    {t : State} (h : KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl kl t) :
    WP isa (.seq (.block [.movw .r9 (BitVec.ofNat 16 H.B), .subs .r9 .r9 (.reg .r8)])
      (.ite .eq (.block []) H.padLoop)) t
      (KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl H.B) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  refine WP.seq (VG.Proof.Hmac.Generic.Arm.wp_movw fun t₁ u₁ => wp_subs (op2_reg _ _) fun t₂ u₂ z₂ =>
    WP.block_nil ?_)
  have e9 : t₁.gpr .r9 - t₁.gpr .r8 = BitVec.ofNat 32 (H.B - kl) := by
    rw [u₁.gpr, u₁.other _ (by decide), h.r8, movw_ofNat (by omega), sub_ofNat hkl]
  have i0 : KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl kl t₂ :=
    ⟨by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], by rw [u₂.sp, u₁.sp, h.sp],
      fun r hr' => by rw [u₂.other r (nm hr' .r9), u₁.other r (nm hr' .r9), h.other r hr'],
      by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8], by rw [u₂.mem, u₁.mem]; exact h.mem⟩
  have hz : t₂.z = decide (kl = H.B) := by
    rw [z₂, e9, VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega)]
    exact decide_eq_decide.mpr (by omega)
  refine WP.ite (decide (kl = H.B)) (by show eval .eq t₂ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0
  · have hlt : kl < H.B := by simp at h0; omega
    rw [padLoop_eq]
    have := count_loop (n := H.B - kl) (by omega)
      (fun k t => KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl (kl + k) t ∧
        t.gpr .r9 = BitVec.ofNat 32 (H.B - (kl + k)))
      (fun k hk t ⟨hk', h9⟩ => WP.mono (pad_step H hr hm (j := kl + k) (by omega) (by omega) hk' h9)
        fun t' ⟨⟨a, b⟩, c⟩ => ⟨⟨by rw [← Nat.add_assoc]; exact a, by rw [b, Nat.add_assoc]⟩,
          by rw [c]; exact decide_eq_decide.mpr (by omega)⟩)
      (s := t₂) ⟨by simpa using i0, by rw [u₂.gpr, e9, Nat.add_zero]⟩
    rw [show kl + (H.B - kl) = H.B by omega] at this
    exact WP.mono this fun _ h => h.1

end VG.Proof.Hmac.Generic.Arm
