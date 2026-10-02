import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Calls of a streaming hash function on 32-bit ARM: the byte loops

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`, with the byte-list lemmas
of `Proof/Hmac/Generic/Common.lean`): the byte copy (`copy`) and the
exclusive-or of `U` into `T`, which the whole of PBKDF2 uses. Each counts `r8`
up from 0 and `r9` down to 0 with `subs`, and branches on its result. Addresses are 32 bits, zero-extended: every buffer the loops touch lies
below 2³², so byte `k` of a buffer at `p + o` is at `State.addr p + o + k`.
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash copy)
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
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => VG.Proof.Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ =>
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
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₀ u₀ => VG.Proof.Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ =>
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

end VG.Proof.Pbkdf2.Stream.Arm

/-!
# HMAC over any streaming hash function on 32-bit ARM: our caller's registers

As on AArch64 (`Proof/Hmac/Generic/AArch64/Init.lean`): the callee-saved
registers we use, and our return address `lr`, are stored in `scratch` after
the working space of the functions we call (`Hash.saved`), with `scratch` in
`r12`, and loaded back at the end, with `scratch` in `r11`, which is loaded
last.
-/

namespace VG.Proof.Pbkdf2.Stream.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
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

/-- A streaming state is kept by what writes elsewhere. -/
theorem repr_keep {H : Hash} (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

end VG.Proof.Pbkdf2.Stream.Arm
