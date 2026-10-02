import VerifiedGarbage.Proof.Hmac.Generic.Arm.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function on 32-bit ARM: the byte loops

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`, with the byte-list lemmas
of `Proof/Hmac/Generic/Common.lean`): the byte copy (`copy`), the exclusive-or
of `U` into `T`, and `init`'s loops that write `K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each
counts `r8` up from 0 and `r9` down to 0 with `subs`, and branches on its
result. Addresses are 32 bits, zero-extended: every buffer the loops touch lies
below 2³², so byte `k` of a buffer at `p + o` is at `State.addr p + o + k`.
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd WP.cons op2_imm op2_reg wp_mov wp_add wp_subs wp_ldrb wp_strb
  eval_ne sub_beq sub_ofNat)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint xorBytes_snoc
  xorBytes_length' InRegions.right' add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge)
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
  omega_nat

/-- Byte `k` of the buffer at `a + o`, as a loop addresses it. -/
theorem addr3 {a : BitVec 32} {k o : Nat} (h : a.toNat + o + k < 2 ^ 32) :
    State.addr (a + BitVec.ofNat 32 k + BitVec.ofNat 32 o) = State.addr a + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega_nat), BitVec.ofNat_add, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat 64 k)]

/-- The flags after counting `r9` down from `n - k` to `n - (k + 1)`. -/
theorem left_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (n - (k + 1) = 0) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega_nat) (by decide)]
  simp only [decide_eq_decide]; omega_nat

theorem left_val {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_nat), Nat.sub_sub]

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
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (n - (k + 1) = 0)) := by
    show eval .ne s' = _; rw [eval_ne, hz]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp; omega_nat, n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

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
    (by rw [u₁.gpr, h.other src hs, h.r8, addr3 (by omega_nat)])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 k) hdo
    (by rw [u₃.gpr, u₂.other dst (nm hd .r12), u₁.other dst (nm hd .r2), h.other dst hd,
      u₂.other .r8 (by decide), u₁.other .r8 (by decide), h.r8, addr3 (by omega_nat)])
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
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_nat)
    rw [hl] at e'
    rw [u₆.mem, u₅.mem, m₄.mem, v, u₃.mem, u₂.mem, u₁.mem, h.mem, bytesAt_snoc', e']
  · rw [z₆, h9, left_z hk (by omega_nat)]

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
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by rw [BitVec.add_comm, BitVec.add_sub_cancel],
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_nat), Nat.lt_irrefl, ↓reduceIte]
  have g11 := h.other .r11 (by decide)
  have g5 := h.other .r5 (by decide)
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := U + BitVec.ofNat 64 k) huo (by rw [u₁.gpr, g11, h.r8, addr3 (by omega_nat)])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₂ u₂ => ?_
  refine wp_add (op2_reg _ _) fun t₃ u₃ => ?_
  have a₃ : State.addr (t₃.gpr .r2 + BitVec.ofNat 32 0) = T + BitVec.ofNat 64 k := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g5, h.r8, addr3 (by omega_nat)]
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
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega_nat)
    rw [hl'] at e'
    rw [u₈.mem, u₇.mem, m₆.mem, hv, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem, e',
      bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [z₈, h9, left_z hk (by omega_nat)]

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
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega_nat
  have rt := hr.keep h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.MdStream.Arm.contains_offset (n := 1) (by omega_nat) (by omega_nat)) hc
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.gpr, rt.r6, h.r8, addr3 (by omega_nat)]; exact congrArg (· + BitVec.ofNat 64 j) (BitVec.add_zero _))
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hm.key j hj) fun t₂ u₂ => ?_
  refine wp_eor (op2_imm (by decide)) fun t₃ u₃ => ?_
  refine wp_add (op2_reg _ _) fun t₄ u₄ => ?_
  have a4 : ∀ o, o + j < 2 ^ 32 - scr.toNat → State.addr (t₄.gpr .r2 + BitVec.ofNat 32 o) =
      State.addr scr + BitVec.ofNat 64 o + BitVec.ofNat 64 j := fun o ho => by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), rt.r11,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8, addr3 (by omega_nat)]
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega_nat) (a4 _ (by omega_nat))
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega_nat)) fun t₅ m₅ => ?_
  refine wp_eor (op2_imm (by decide)) fun t₆ u₆ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [u₆.other _ (by decide), m₅.gpr, a4 _ (by omega_nat)]; simp only [P, add_ofNat_add])
    (by rw [u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega_nat))
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
    by rw [u₉.gpr, h9', left_val hj]⟩, by rw [z₉, h9', left_z hj (by omega_nat)]⟩
  have r12 : t₃.gpr .r12 = (t.mem (K + BitVec.ofNat 64 j)).setWidth 32 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
  have v₁ : (t₄.gpr .r1).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.ipad := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem, pad_byte32, hbyte, ipad32]
  have v₂ : (t₆.gpr .r1).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.opad := by
    rw [u₆.gpr, m₅.gpr, u₄.other .r12 (by decide), r12, pad_byte32, hbyte, opad32]
  rw [u₉.mem, u₈.mem, m₇.mem, v₂, u₆.mem, m₅.mem, v₁, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact buf_write h.mem hB (by omega_nat) hl

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
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega_nat
  have rt := hr.keep h.other
  refine wp_add (op2_reg _ _) fun t₁ u₁ => ?_
  have a1 : ∀ o, o + j < 2 ^ 32 - scr.toNat → State.addr (t₁.gpr .r2 + BitVec.ofNat 32 o) =
      State.addr scr + BitVec.ofNat 64 o + BitVec.ofNat 64 j := fun o ho => by
    rw [u₁.gpr, rt.r11, h.r8, addr3 (by omega_nat)]
  refine wp_mov (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega_nat) (by rw [u₂.other _ (by decide)]; exact a1 _ (by omega_nat))
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega_nat)) fun t₃ m₃ => ?_
  refine wp_mov (op2_imm (by decide)) fun t₄ u₄ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j) hbuf
    (by rw [u₄.other _ (by decide), m₃.gpr, u₂.other _ (by decide), a1 _ (by omega_nat)]; simp only [P, add_ofNat_add])
    (by rw [u₄.wr, m₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega_nat)) fun t₅ m₅ => ?_
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
    by rw [z₇, h9', left_z hj' (by omega_nat)]⟩
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
  · have hpos : 0 < kl := by simp at h0; omega_nat
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
    rw [u₁.gpr, u₁.other _ (by decide), h.r8, movw_ofNat (by omega_nat), sub_ofNat hkl]
  have i0 : KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl kl t₂ :=
    ⟨by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], by rw [u₂.sp, u₁.sp, h.sp],
      fun r hr' => by rw [u₂.other r (nm hr' .r9), u₁.other r (nm hr' .r9), h.other r hr'],
      by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8], by rw [u₂.mem, u₁.mem]; exact h.mem⟩
  have hz : t₂.z = decide (kl = H.B) := by
    rw [z₂, e9, VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega_nat)]
    exact decide_eq_decide.mpr (by omega_nat)
  refine WP.ite (decide (kl = H.B)) (by show eval .eq t₂ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0
  · have hlt : kl < H.B := by simp at h0; omega_nat
    rw [padLoop_eq]
    have := count_loop (n := H.B - kl) (by omega_nat)
      (fun k t => KeyInv H s₀ (State.addr scr + BitVec.ofNat 64 H.buf) (State.addr kp) kl (kl + k) t ∧
        t.gpr .r9 = BitVec.ofNat 32 (H.B - (kl + k)))
      (fun k hk t ⟨hk', h9⟩ => WP.mono (pad_step H hr hm (j := kl + k) (by omega_nat) (by omega_nat) hk' h9)
        fun t' ⟨⟨a, b⟩, c⟩ => ⟨⟨by rw [← Nat.add_assoc]; exact a, by rw [b, Nat.add_assoc]⟩,
          by rw [c]; exact decide_eq_decide.mpr (by omega_nat)⟩)
      (s := t₂) ⟨by simpa using i0, by rw [u₂.gpr, e9, Nat.add_zero]⟩
    rw [show kl + (H.B - kl) = H.B by omega_nat] at this
    exact WP.mono this fun _ h => h.1

end VG.Proof.Hmac.Generic.Arm

/-!
# HMAC over any streaming hash function on 32-bit ARM: our caller's registers

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`): the callee-saved
registers we use, and our return address `lr`, are stored in `scratch` after
the working space of the functions we call (`Hash.saved`), with `scratch` in
`r12`, and loaded back at the end, with `scratch` in `r11`, which is loaded
last.
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd wp_ldr saveMem saveList_ok readW_writeW_save sub_offset)
open VG.Proof.Hmac.Generic.Common (InRegions.right' add_ofNat_add)

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr, .r11]

theorem preserved_saved : ∀ r ∈ preserved, r ∈ savedRegs := by decide

/-- Where the registers are saved. -/
abbrev saveR (scr : BitVec 32) : Region := ⟨State.addr scr + BitVec.ofNat 64 (8 * H.W), 36⟩

/-- The registers of `s₀` saved in the memory `m`. -/
def SavedRegs (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ H.saved, m.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

theorem saved_mem {p : Reg × Nat} (hp : p ∈ H.saved) : 8 * H.W ≤ p.2 ∧ p.2 + 4 ≤ 8 * H.W + 36 := by
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega_nat

theorem saved_pairwise : H.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  simp [Hash.saved]

/-- Slot `d` of the save area. -/
theorem slot_sub (scr : BitVec 32) {d : Nat} (h₁ : 8 * H.W ≤ d) (h₂ : d + 4 ≤ 8 * H.W + 36) :
    Region.Sub ⟨State.addr scr + BitVec.ofNat 64 d, 4⟩ (saveR H scr) := by
  rw [show d = 8 * H.W + (d - 8 * H.W) by omega_nat, ← add_ofNat_add]
  exact sub_offset (by omega_nat) (by omega_nat)

theorem SavedRegs.frame {scr : BitVec 32} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := fun p hp => by
  obtain ⟨h₁, h₂⟩ := saved_mem H hp
  rw [← h p hp]
  exact hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (slot_sub H scr h₁ h₂)) (by decide)

theorem saveMem_other (m : Mem) (B : Addr) (g : Reg → BitVec 32) {d : Nat} (hd : d < 2 ^ 32) :
    ∀ l : List (Reg × Nat), (∀ q ∈ l, q.2 < 2 ^ 32 ∧ (d + 4 ≤ q.2 ∨ q.2 + 4 ≤ d)) →
    (saveMem m B g l).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32
  | [], _ => rfl
  | q :: l, h => by
    rw [saveMem, saveMem_other _ B g hd l fun q' hq' => h q' (List.mem_cons_of_mem _ hq'),
      readW_writeW_save _ _ _ hd (h q (by simp)).1 (h q (by simp)).2]

theorem saveMem_read (B : Addr) (g : Reg → BitVec 32) :
    ∀ (m : Mem) (l : List (Reg × Nat)), l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    (∀ p ∈ l, p.2 < 2 ^ 32) → ∀ p ∈ l, (saveMem m B g l).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1
  | _, [], _, _, p, hp => by cases hp
  | m, q :: l, hpw, hb, p, hp => by
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [saveMem, saveMem_other _ _ _ (hb p (by simp)) l
        (fun q' hq' => ⟨hb q' (List.mem_cons_of_mem _ hq'), hpw.1 q' hq'⟩), Mem.readW_writeW_self32]
    · rw [saveMem]
      exact saveMem_read B g _ l hpw.2 (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq')) p hp

theorem saveMem_frameR (B : Addr) (g : Reg → BitVec 32) (o L : Nat) (hL : o + L < 2 ^ 64) :
    ∀ (m : Mem) (l : List (Reg × Nat)), (∀ p ∈ l, o ≤ p.2 ∧ p.2 + 4 ≤ o + L) →
    Frame [⟨B + BitVec.ofNat 64 o, L⟩] m (saveMem m B g l)
  | _, [], _ => Frame.refl _ _
  | m, p :: l, hl => by
    obtain ⟨h₁, h₂⟩ := hl p (by simp)
    have c : (⟨B + BitVec.ofNat 64 o, L⟩ : Region).Contains (B + BitVec.ofNat 64 p.2) (32 / 8) := by
      rw [show p.2 = o + (p.2 - o) by omega_nat, ← add_ofNat_add]
      exact contains_offset (by omega_nat) (by omega_nat)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c).trans
      (saveMem_frameR B g o L hL _ l fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem save_eq : H.save = H.saved.map (fun p => Instr.str p.1 .r12 p.2) := rfl

/-- Saving the registers, with `scratch` in `r12`. -/
theorem save_ok {s : State} {scr : BitVec 32} {L : Nat} (h12 : s.gpr .r12 = scr) (hW : H.W ≤ 64)
    (hsc : ⟨State.addr scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [h12]
    exact ⟨by omega_nat, by omega_nat, ⟨_, hsc, contains_offset (by omega_nat) (by omega_nat)⟩⟩
  · rw [m, h12]
    exact saveMem_frameR _ _ _ _ (by omega_nat) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, h12]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega_nat) p hp

theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

/-- The slots loaded before `r11`. -/
def saved8 : List (Reg × Nat) :=
  [(.r4, 8 * H.W), (.r5, 8 * H.W + 4), (.r6, 8 * H.W + 8), (.r7, 8 * H.W + 12), (.r8, 8 * H.W + 16),
    (.r9, 8 * H.W + 20), (.r10, 8 * H.W + 24), (.lr, 8 * H.W + 28)]

theorem restore_eq :
    H.restore = (saved8 H).map (fun p => Instr.ldr p.1 .r11 p.2) ++ ([.ldr .r11 .r11 (8 * H.W + 32)] : List Instr) := rfl

theorem saved8_fst : (saved8 H).map Prod.fst = [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr] := rfl

theorem saved8_sub {p : Reg × Nat} (hp : p ∈ saved8 H) : p ∈ H.saved := by
  simp only [saved8, Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with h | h | h | h | h | h | h | h <;> simp [h]

/-- Loading them back, with `scratch` in `r11` (loaded last). -/
theorem restore_ok {s : State} {scr : BitVec 32} {L : Nat} (h11 : s.gpr .r11 = scr) (hW : H.W ≤ 64)
    {s₀ : State} (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨State.addr scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 36 ≤ L)
    (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {d}, d + 4 ≤ L →
      InRegions (t.rd ++ t.wr) (State.addr scr + BitVec.ofNat 64 d) 4 := fun hr hw d hd => by
    rw [hr, hw]; exact InRegions.right' ⟨_, hsc, contains_offset hd (by omega_nat)⟩
  rw [restore_eq]
  refine restoreList_ok (saved8 H) s _ (by rw [saved8_fst]; decide) (fun p hp => ?_)
    fun s₁ hl ho hm hrd hwr hsp => ?_
  · have := saved_mem H (saved8_sub H hp)
    refine ⟨?_, by omega_nat, by rw [h11]; omega_nat, by rw [h11]; exact io rfl rfl (by omega_nat)⟩
    simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  have e11 : s₁.gpr .r11 = scr := by
    rw [ho _ (by rw [saved8_fst]; decide), h11]
  refine wp_ldr (by omega_nat) (addr_add (by rw [e11]; omega_nat)) (by rw [e11]; exact io hrd hwr (by omega_nat))
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, hm], by rw [u.rd, hrd], by rw [u.wr, hwr], by rw [u.sp, hsp],
      fun r hr => ?_, fun r hr => ?_⟩
  · have hv : ∀ p ∈ saved8 H, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
      have h1 : p.1 ≠ .r11 := by
        simp only [saved8, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)
      rw [u.other _ h1, hl p hp, h11, hs p (saved8_sub H hp)]
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv (.r4, 8 * H.W) (by simp [saved8])
    · exact hv (.r5, 8 * H.W + 4) (by simp [saved8])
    · exact hv (.r6, 8 * H.W + 8) (by simp [saved8])
    · exact hv (.r7, 8 * H.W + 12) (by simp [saved8])
    · exact hv (.r8, 8 * H.W + 16) (by simp [saved8])
    · exact hv (.r9, 8 * H.W + 20) (by simp [saved8])
    · exact hv (.r10, 8 * H.W + 24) (by simp [saved8])
    · exact hv (.lr, 8 * H.W + 28) (by simp [saved8])
    · rw [u.gpr, e11, hm, hs (.r11, 8 * H.W + 32) (by simp [Hash.saved])]
  · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u.other r hr.2.2.2.2.2.2.2.2, ho r (by
      rw [saved8_fst]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1⟩)]

theorem saved_ne {p : Reg × Nat} (hp : p ∈ H.saved) {r : Reg} (hr : r ∉ savedRegs) : p.1 ≠ r := by
  rintro rfl
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hr

/-- The registers saved from a state that agrees on them. -/
theorem SavedRegs.of_eq {scr : BitVec 32} {s₀ s₁ : State} {m : Mem} (h : SavedRegs H scr s₁ m)
    (he : ∀ r ∈ savedRegs, s₁.gpr r = s₀.gpr r) : SavedRegs H scr s₀ m := fun p hp => by
  rw [h p hp]
  refine he _ ?_
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## Odds and ends -/

theorem below_eq {s t : State} (h : s.sp = t.sp) : below s = below t := by simp only [below, h]

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_nat)

theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) : Covers [r] rs :=
  Covers.of_sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'
    exact ⟨r, h, 0, by rw [hr']; simp, by rw [hr']; simp⟩

end VG.Proof.Hmac.Generic.Arm

/-!
# HMAC over any streaming hash function on 32-bit ARM: `init`, correct

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`). `scratch` is a stack
argument, loaded into `r12` first; every callee-saved register (and `lr`) is
saved in it, and loaded back at the end. The functions we call keep
`r4`–`r11`, which hold our variables.
-/

namespace VG.Proof.Hmac.Generic.Arm.Init

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash scrAt)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.MdStream.Arm (contains_offset)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_cmp wp_ldrSp op2_imm op2_reg sub_offset
  ofNat_beq_zero)
open VG.Proof.Hmac.Generic.Common (add_ofNat_add bytesAt_prefix_congr inRegions_of_sub K0 K0_length
  off_disj off_disj0 sub_of_off sub_of_self bytes_keep take_map_xor)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev out : BitVec 32 := s₀.gpr .r1
abbrev kp : BitVec 32 := s₀.gpr .r2
abbrev kl : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev inR : Region := ⟨State.addr (inn s₀), H.S⟩
abbrev outR : Region := ⟨State.addr (out s₀), H.S⟩
abbrev keyR : Region := ⟨State.addr (kp s₀), kl s₀⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 8 * sc⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stkR : Region := below s₀
/-- The padded keys. -/
abbrev P : Addr := State.addr (scr s₀) + BitVec.ofNat 64 H.buf
abbrev bufR : Region := ⟨P (H := H) s₀, 2 * H.B⟩
abbrev calR : Region := ⟨State.addr (scr s₀), hH.Wb⟩
/-- Byte `o` of `scratch`, as a register holds it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o

end

theorem kl_lt (s₀ : State) : kl s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (out s₀).toNat + H.S ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.buf + 2 * H.B ≤ 8 * sc
  hB : H.B ≤ 128
  hW : H.W ≤ 64
  hS : H.S ≤ 256

theorem pre_of {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.buf + 2 * H.B ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, h8, h9, h10, h11, h12, h13, _, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h15, h16, h17, h18, h19, h20, h21, hfit, hH.hBB,
    hH.hW, hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) :
    Region.Sub ⟨State.addr (scr s₀) + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega_nat)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; simp only [Hash.buf] at this; exact sub_sc hp (by omega_nat)

theorem buf_sub : Region.Sub (bufR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw
  exact sub_offset hp.fits (by omega_nat)

omit hp in
theorem padI_sub : Region.Sub ⟨P (H := H) s₀, H.B⟩ (bufR (H := H) s₀) := Region.sub_prefix (by omega_nat)

theorem padO_sub : Region.Sub ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (bufR (H := H) s₀) :=
  sub_offset (by omega_nat) (by have := hp.hB; omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.hW
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 36) (by omega_nat) (by omega_nat)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hB
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 36) (n := 2 * H.B) (by omega_nat) (by omega_nat)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.hW; have := hp.hB
  exact off_disj _ (a := 8 * H.W) (m := 36) (b := 8 * H.W + 36) (n := 2 * H.B) (by omega_nat) (by omega_nat)
    (by omega_nat)

theorem addr_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) :
    State.addr (dO s₀ o) = State.addr (scr s₀) + BitVec.ofNat 64 o :=
  addr_add (by have := hp.nw; omega_nat)

theorem toNat_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_nat), Nat.mod_eq_of_lt (by omega_nat)]

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = inn s₀
  r5 : s.gpr .r5 = out s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r11]

/-- `KR` survives changes to other registers, and to memory away from the
save area. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r11, h.saved.frame H hf hs⟩

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem (State.addr (kp s₀)) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) s₀) := by
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf
  have hsc : ⟨State.addr (scr s₀), 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq ?_
  simp only [Hash.initPrologue, List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl (by rw [hp.rd]; exact ⟨argR s₀, by simp,
    Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (by omega_nat) (by omega_nat)
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have h4 : s₉.gpr .r4 = inn s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, e₂ _ (by decide)]
  have h5 : s₉.gpr .r5 = out s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), e₂ _ (by decide)]
  have h6 : s₉.gpr .r6 = kp s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
  have h11 : s₉.gpr .r11 = scr s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl
  have h8 : s₉.gpr .r8 = BitVec.ofNat 32 0 := by rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr]; rfl
  have h9 : s₉.gpr .r9 = BitVec.ofNat 32 (kl s₀) := by
    rw [f₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hz : s₉.z = decide (kl s₀ = 0) := by
    have h9' : s₈.gpr .r9 = BitVec.ofNat 32 (kl s₀) := by rw [← f₉.gpr]; exact h9
    rw [z₉, h9', show ∀ x : BitVec 32, x - 0 = x from fun x => BitVec.sub_zero x,
      ofNat_beq_zero (s₀.gpr .r3).isLt]
  have hm₉ : s₉.mem = s₂.mem := by rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hrd : s₉.rd = s₀.rd := by rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have hwr : s₉.wr = s₀.wr := by rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have hsp : s₉.sp = s₀.sp := by rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  have hr : LoopRegs (scr s₀) (kp s₀) s₉ := ⟨h11, h6⟩
  have hm : LoopMem H (scr s₀) (kp s₀) (kl s₀) s₉ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (Nat.lt_trans (kl_lt s₀) (by decide))
          hk |>.elim fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by
        rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega_nat) hk,
      hp.k_s.sub_right (buf_sub hp), hB, by simp only [Hash.buf]; omega_nat, by simp only [Hash.buf]; omega_nat,
      hp.nk⟩
  refine WP.seq (WP.mono (key_ok H hr hm h8 h9 hz) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₉.mem := by rw [hm₉, ← u₁.mem]; exact f₂
  have eK : K0 s₉.mem (State.addr (kp s₀)) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp))) (Nat.le_of_lt (Nat.lt_trans (kl_lt s₀) (by decide))) hi
  have hg : ∀ r ∉ clob, t.gpr r = s₉.gpr r := ht.other
  have sv : SavedRegs H (scr s₀) s₀ s₉.mem := hm₉ ▸ sv₂.of_eq H fun r hr => u₁.other r (by
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [ht.sp, hsp],
    by rw [hg _ (by decide), h4], by rw [hg _ (by decide), h5], by rw [hg _ (by decide), h11],
    sv.frame H ht.mem.frame (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp)⟩,
    ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem state_disj {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨State.addr p, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨State.addr p, H.S⟩ ∧
      p.toNat + H.S ≤ 2 ^ 32 := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.ni⟩
  · exact ⟨hp.o_s, hp.b_o, hp.no⟩

theorem state_in {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨State.addr p, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem kr_mov {s t : State} (hk : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s t d v) : KR (H := H) s₀ t :=
  hk.keep u.rd u.wr u.sp (fun r hr => u.other r fun h => hd (h ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

/-- `KR` after a call that writes `rs`. -/
theorem kr_after {t s' : State} (hk : KR (H := H) s₀ t) {rs : List Region} (ha : After t rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [below_eq hk.sp] at f
  refine hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f ?_
  simp only [List.mem_append, List.mem_singleton]
  rintro r (hr | rfl)
  · exact hs r hr
  · exact hp.b_s.symm.sub_left (save_sub hp)

omit hp in
theorem initArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32} (hs : s.gpr st = p) :
    WP isa (.block [.mov .r0 (.reg st)]) s fun t => KR (H := H) s₀ t ∧ t.gpr .r0 = p ∧ t.mem = s.mem :=
  wp_mov (op2_reg _ _) fun _ u₁ => WP.block_nil ⟨kr_mov hk (by decide) u₁, by rw [u₁.gpr, hs], u₁.mem⟩

theorem initCall_ok {t : State} (hk : KR (H := H) s₀ t) {p : BitVec 32} (hd : t.gpr .r0 = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, stkR s₀] t.mem s'.mem →
      hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (.call H.initN H.initC) t Q := by
  obtain ⟨dS, _, np⟩ := state_disj hp hpR
  refine init_call hH hd np (by rw [hk.wr]; exact covers_one (state_in hp hpR)) fun s' ha hr => ?_
  have f := ha.frame
  rw [below_eq hk.sp] at f
  exact hQ s' (kr_after hp hk ha (by
    simp only [List.mem_singleton]; rintro r rfl; exact dS.symm.sub_left (save_sub hp))) f hr

theorem callInit_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32} (hs : s.gpr st = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, stkR s₀] s.mem s'.mem →
      hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (H.callInit st) s Q :=
  WP.seq (WP.mono (initArgs_ok hk hs) fun _ ⟨k, d, m⟩ =>
    initCall_ok hH hp k d hpR fun s' k' f r => hQ s' k' (m ▸ f) r)

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block (([.mov .r0 (.reg st)] : List Instr) ++ scrAt .r1 o ++ ([.movw .r7 (BitVec.ofNat 16 H.B),
        .mov .r10 (.reg .r11), .movw .r2 (BitVec.ofNat 16 0), .mov .r3 (.imm 0)] : List Instr))) s fun t =>
      KR (H := H) s₀ t ∧ UpdArgs hH t p (dO s₀ o) (scr s₀) H.B ∧ count t = BitVec.ofNat 64 0 ∧
        t.mem = s.mem := by
  obtain ⟨dS, dK, np⟩ := state_disj hp hpR
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o + H.B ≤ 8 * sc := by omega_nat
  have ea := addr_dO hp (o := o) (by omega_nat)
  have dsub : Region.Sub ⟨State.addr (dO s₀ o), H.B⟩ (bufR (H := H) s₀) := by
    rw [ea]
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨State.addr (dO s₀ o), H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_movw fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_movw fun s₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have k₇ : KR (H := H) s₀ s₇ :=
    kr_mov (kr_mov (kr_mov (kr_mov (kr_mov (kr_mov (kr_mov hk (by decide) u₁) (by decide) u₂) (by decide) u₃)
      (by decide) u₄) (by decide) u₅) (by decide) u₆) (by decide) u₇
  have h11 : s.gpr .r11 = scr s₀ := hk.r11
  have hm : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₇, ?_, count_movw (c := 0) (by decide) (by rw [u₇.other _ (by decide), u₆.gpr]) u₇.gpr, hm⟩
  exact
    { r0 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs]
      r1 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h11,
          movw_ofNat (by omega_nat)]
      r7 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
          movw_ofNat (by omega_nat)]
      r10 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h11]
      hlen := by omega_nat
      sp16 := by rw [k₇.sp]; exact hp.sp16
      cd := by
        rw [k₇.rd, k₇.wr, ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.rd, hp.wr]; simp) ho'
      cw := by
        rw [k₇.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨State.addr p, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega_nat)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      b_st := by rw [below_eq k₇.sp]; exact dK
      b_d := by rw [below_eq k₇.sp]; exact hp.b_s.sub_right dsc
      b_sc := by rw [below_eq k₇.sp]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := np
      nd := by rw [toNat_dO hp (by omega_nat)]; omega_nat
      nsc := by have := hH.hWb; omega_nat }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) {p d : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀)
    (ha : UpdArgs hH t p d (scr s₀) H.B) (hc : count t = BitVec.ofNat 64 0) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem (State.addr p) [] →
        hH.SH.Repr s'.mem (State.addr p) ([] ++ bytesAt t.mem (State.addr d) H.B)) → Q s') :
    WP isa (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) t Q := by
  obtain ⟨dS, _⟩ := state_disj hp hpR
  refine upd_frame hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [below_eq hk.sp] at f
  refine hQ s' (kr_after hp hk ha' ?_) f fun hr => hpost [] hr (by rw [hc]; rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact dS.symm.sub_left (save_sub hp)
  · exact (cal_save hH hp).symm

theorem callUpd_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem (State.addr p) [] →
        hH.SH.Repr s'.mem (State.addr p) ([] ++ bytesAt s.mem (State.addr (scr s₀) + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [.mov .r0 (.reg st)] 0 o H.B) s Q := by
  have hf := hp.fits; have := hp.hB; have ho' := ho; simp only [Hash.buf] at hf ho'
  have ea := addr_dO hp (o := o) (by omega_nat)
  exact WP.seq (WP.mono (updArgs_ok hH hp hk hs hpR ho) fun t ⟨k, a, c, m⟩ =>
    updCall_ok hH hp k hpR a c fun s' k' f r => hQ s' k' (m ▸ f) fun hr => by
      have := r (m ▸ hr); rwa [m, ea] at this)

/-! ## Correctness -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.Common.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega_nat,
    ↓reduceIte]

omit hp in
/-- The end: `abiPreserved`, from `KR` and `restore`. -/
theorem abi_of {s s' : State} (hk : KR (H := H) s₀ s) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) : abiPreserved s₀ s' :=
  ⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, hk.sp]⟩

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
    hp.b_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dOK : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (stkR s₀) :=
    hp.b_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dOC : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (calR hH s₀) :=
    (cal_buf hH hp).symm.sub_left (padO_sub hp)
  have eO : State.addr (scr s₀) + BitVec.ofNat 64 (H.buf + H.B) = P (H := H) s₀ + BitVec.ofNat 64 H.B := by
    rw [P, add_ofNat_add]
  refine WP.seq (WP.mono (keys_ok sc hp) fun s₁ h₁ => ?_)
  refine WP.seq (callInit_ok hH hp h₁.kr (st := .r4) h₁.kr.r4 (.inl rfl) fun s₂ k₂ f₂ r₂ => ?_)
  have bI₂ := (bytes_keep f₂ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans h₁.bufI
  have bO₂ := (bytes_keep f₂ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans h₁.bufO
  refine WP.seq (callUpd_ok hH hp k₂ k₂.r4 (.inl rfl) (.inl rfl) fun s₃ k₃ f₃ r₃ => ?_)
  have rI₃ := r₃ r₂
  rw [List.nil_append, bI₂] at rI₃
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans bO₂
  refine WP.seq (callInit_ok hH hp k₃ (st := .r5) k₃.r5 (.inr rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := repr_keep hH f₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.b_i.symm) rI₃
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> with_reducible assumption)
    (by omega_nat)).trans bO₃
  refine WP.seq (callUpd_ok hH hp k₄ k₄.r5 (.inr rfl) (.inr rfl) fun s₅ k₅ f₅ r₅ => ?_)
  have rO₅ := r₅ r₄
  rw [List.nil_append, eO, bO₄] at rO₅
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.b_i.symm) rI₄
  have hsc : ⟨State.addr (scr s₀), 8 * sc⟩ ∈ s₅.wr := by rw [k₅.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₅.r11 hW k₅.saved hsc (by omega_nat) hp.nw) fun s' ⟨hm, _, _, hsp, hg, _⟩ => ?_
  refine ⟨abi_of k₅ hsp hg, ?_⟩
  show hH.SH.Repr s'.mem (State.addr (inn s₀)) _ ∧ hH.SH.Repr s'.mem (State.addr (out s₀)) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨rI₅, rO₅⟩

end

end VG.Proof.Hmac.Generic.Arm.Init
