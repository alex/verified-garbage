import VerifiedGarbage.Proof.Hmac.Generic.X86.Hash
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function on x86 (32-bit): `init`, correct

The byte loops, our caller's registers, then `init` (one module, as nothing
else imports the first two).
-/

/-!
## The byte loops

As on the other targets
(`Proof/Hmac/Generic/Arm/Init.lean`, whose byte-list lemmas from x86-64
are reused): the byte copy (`copy`), the exclusive-or of `U` into `T`, and
`init`'s loops that write `K₀ ⊕ ipad` and `K₀ ⊕ opad`. Each counts an index
up from 0 and compares it with its bound. The model has no index registers,
so each access computes its address first: byte `k` of a buffer at
`p + o` is at `[x + o]` with `x = p + k`, which is `p + o + k`, as nothing
wraps around the 32-bit address space.
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash copy at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd WP.cons wp_mov wp_movi wp_add wp_addi wp_cmp wp_cmpi wp_test
  wp_movzx8 wp_store8 sub_beq sub_ofNat eval_e eval_ne ofNat_beq_zero)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint xorBytes_snoc xorBytes_length'
  InRegions.right' add_ofNat_add BufMem buf_write K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xor {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem ofNat_succ32 (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

/-- Byte `k` of the buffer at `a + o`, as a loop addresses it. -/
theorem addr3 {a : BitVec 32} {k o : Nat} (h : a.toNat + o + k < 2 ^ 32) :
    addr (a + BitVec.ofNat 32 k) o = a.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  rw [VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega_nat), add_ofNat_add, Nat.add_comm]

/-- The flags after counting up to `k + 1 ≤ n`. -/
theorem count_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (k + 1) - BitVec.ofNat 32 n == 0) = decide (k + 1 = n) :=
  sub_beq (by omega_nat) hn

/-- The registers the loops write. -/
abbrev clob : List Reg := [.eax, .ecx, .edx, .ebx]

/-- The registers `copy` writes. -/
abbrev cclob : List Reg := [.eax, .ecx, .edx]

theorem not_cclob {r : Reg} (h : r ∉ clob) : r ∉ cclob := fun hc =>
  h (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; tauto)

theorem nm {r : Reg} {l : List Reg} (h : r ∉ l) (x : Reg) (hx : x ∈ l := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `ne` that runs its body `n > 0` times, each run
ending with the flags of `k + 1 = n`. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s → WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

/-! ## `copy` -/

/-- After `k` bytes of a `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ∉ cclob) (hd : dst ∉ cclob)
    {so d n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State}
    (hsw : (s.gpr src).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr dst).toNat + d + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr src).setWidth 64 + BitVec.ofNat 64 so, n⟩
      ⟨(s.gpr dst).setWidth 64 + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      Copied s ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d)
        (bytesAt s.mem ((s.gpr src).setWidth 64 + BitVec.ofNat 64 so) n) t := by
  set A := (s.gpr src).setWidth 64 + BitVec.ofNat 64 so
  set B := (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d
  refine WP.seq (wp_movi fun s₀ u₀ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r hr => u₀.other r (nm hr .ecx), u₀.gpr,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (count_loop hn (CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.other src hs, h.ecx, addr3 (by omega_nat)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_at, u₅.gpr, u₄.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), u₃.other _ (nm hd .edx), u₂.other _ (nm hd .eax),
      u₁.other _ (nm hd .eax), h.other dst hd, h.ecx, addr3 (by omega_nat)])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₆ m₆ => ?_
  refine wp_addi fun t₇ u₇ => wp_cmpi fun t₈ f₈ _ z₈ => WP.block_nil ?_
  have h7 : t₇.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx, ofNat_succ32]
  refine ⟨⟨by rw [f₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₈.gpr, u₇.other r (nm hr .ecx), m₆.gpr, u₅.other r (nm hr .eax), u₄.other r (nm hr .eax),
        u₃.other r (nm hr .edx), u₂.other r (nm hr .eax), u₁.other r (nm hr .eax), h.other r hr],
    by rw [f₈.gpr, h7], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₅.gpr .edx).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.mem]
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega_nat)
    rw [hl] at e'
    rw [f₈.mem, u₇.mem, m₆.mem, show Reg8.dl.reg = .edx from rfl, v, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      h.mem, bytesAt_snoc', e']
  · rw [z₈, h7, count_z hk hn']

/-! ## The exclusive-or of `U` into `T` -/

theorem xor_byte32 (a b : Byte) : ((a.setWidth 32 ^^^ b.setWidth 32).setWidth 8) = b ^^^ a := by
  ext i hi
  simp [BitVec.getElem_xor, Bool.xor_comm]

/-- After `k` bytes of the exclusive-or of `[U]` into `[T]`. -/
structure XorInv (s : State) (U T : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = writeBytes s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))

/-- `T ← T ⊕ U`, `n` bytes, with `U` at `ebp + uo` and `T` at `esi`. -/
theorem xor_ok {uo n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State}
    (huw : (s.gpr .ebp).toNat + uo + n ≤ 2 ^ 32) (htw : (s.gpr .esi).toNat + n ≤ 2 ^ 32)
    (hinU : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo + BitVec.ofNat 64 k) 1)
    (houtT : ∀ k < n, InRegions s.wr ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo, n⟩ ⟨(s.gpr .esi).setWidth 64, n⟩) :
    WP isa (.seq (.block [.mov .ecx (.imm 0)])
      (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (at_ .eax uo),
        .mov .eax (.reg .esi), .alu .add .eax (.reg .ecx), .movzx8 .ebx (at_ .eax 0), .alu .xor .edx (.reg .ebx),
        .store8 (at_ .eax 0) .dl, .alu .add .ecx (.imm 1), .alu .cmp .ecx (.imm (BitVec.ofNat 32 n))]) .ne)) s
      fun t => XorInv s ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo) ((s.gpr .esi).setWidth 64) n t := by
  set U := (s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 uo
  set T := (s.gpr .esi).setWidth 64
  refine WP.seq (wp_movi fun s₀ u₀ => WP.block_nil ?_)
  have i0 : XorInv s U T 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r hr => u₀.other r (nm hr .ecx), u₀.gpr,
      by rw [u₀.mem]; simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil]⟩
  refine count_loop hn (XorInv s U T) (fun k hk t h => ?_) i0
  have hl : (bytesAt s.mem T k).length = k := bytesAt_length _ _ _
  have hl' : (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k)).length = k := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), hl]
  have rU : t.mem (U + BitVec.ofNat 64 k) = s.mem (U + BitVec.ofNat 64 k) := by
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_nat), Nat.lt_irrefl, ↓reduceIte]
  have gb := h.other .ebp (by decide)
  have gs := h.other .esi (by decide)
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := U + BitVec.ofNat 64 k)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), gb, h.ecx, addr3 (by omega_nat)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  have a₅ : t₅.ea (at_ .eax 0) = T + BitVec.ofNat 64 k := by
    rw [ea_at, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gs, h.ecx,
      addr3 (by omega_nat)]
    exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _)
  refine wp_movzx8 (a := T + BitVec.ofNat 64 k) a₅
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]
        exact InRegions.right' (houtT k hk)) fun t₆ u₆ => ?_
  refine wp_xor fun t₇ u₇ => ?_
  refine wp_store8 (a := T + BitVec.ofNat 64 k)
    (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide)]; exact a₅)
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact houtT k hk) fun t₈ m₈ => ?_
  refine wp_addi fun t₉ u₉ => wp_cmpi fun t₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  have h9 : t₉.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₉.gpr, m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.ecx,
      ofNat_succ32]
  refine ⟨⟨by rw [f₁₀.rd, u₉.rd, m₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₁₀.wr, u₉.wr, m₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₁₀.gpr, u₉.other r (nm hr .ecx), m₈.gpr, u₇.other r (nm hr .edx), u₆.other r (nm hr .ebx),
        u₅.other r (nm hr .eax), u₄.other r (nm hr .eax), u₃.other r (nm hr .edx), u₂.other r (nm hr .eax),
        u₁.other r (nm hr .eax), h.other r hr],
    by rw [f₁₀.gpr, h9], ?_⟩, ?_⟩
  · have hv : (t₇.gpr .edx).setWidth 8 = s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k) := by
      rw [u₇.gpr, u₆.other .edx (by decide), u₆.gpr, u₅.other .edx (by decide),
        u₄.other .edx (by decide), u₃.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, xor_byte32, rU, rT]
    have e' := writeBytes_snoc s.mem T (Spec.Pbkdf2.xorBytes (bytesAt s.mem T k) (bytesAt s.mem U k))
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega_nat)
    rw [hl'] at e'
    rw [f₁₀.mem, u₉.mem, m₈.mem, show Reg8.dl.reg = .edx from rfl, hv, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem, h.mem, e', bytesAt_snoc', bytesAt_snoc', xorBytes_snoc _ _ _ _ (by simp [bytesAt_length])]
  · rw [z₁₀, h9, count_z hk hn']

/-! ## `init`'s key and pad loops

`K₀ ⊕ ipad` is written at `P = scratch + buf` and `K₀ ⊕ opad` at `P + B`,
byte by byte (as on x86-64, `BufMem`): first the key's `kl` bytes (read at
`K`), then the zeros that pad it to `B`. `ebx` is the index, `esi` the key,
`edi` its length and `ebp` `scratch`. -/

variable (H : Hash)

/-- Where the loops are. -/
structure LoopRegs (scr kp : BitVec 32) (kl : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = scr
  esi : s.gpr .esi = kp
  edi : s.gpr .edi = BitVec.ofNat 32 kl

theorem LoopRegs.keep {scr kp : BitVec 32} {kl : Nat} {s t : State} (h : LoopRegs scr kp kl s)
    (hk : ∀ r ∉ clob, t.gpr r = s.gpr r) : LoopRegs scr kp kl t :=
  ⟨by rw [hk _ (by decide), h.ebp], by rw [hk _ (by decide), h.esi], by rw [hk _ (by decide), h.edi]⟩

/-- The loops' invariant, from the state `s` they start in. -/
structure KeyInv (s : State) (P K : Addr) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  ebx : t.gpr .ebx = BitVec.ofNat 32 j
  mem : BufMem H.B P (K0 s.mem K kl H.B) s.mem j t.mem

/-- The regions the loops access, and the sizes. -/
structure LoopMem (scr kp : BitVec 32) (kl : Nat) (s : State) : Prop where
  kl_le : kl ≤ H.B
  key : ∀ k < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 k) 1
  buf : ∀ k < 2 * H.B, InRegions s.wr (scr.setWidth 64 + BitVec.ofNat 64 H.buf + BitVec.ofNat 64 k) 1
  disj : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨scr.setWidth 64 + BitVec.ofNat 64 H.buf, 2 * H.B⟩
  hB : H.B ≤ 128
  nscr : scr.toNat + H.buf + 2 * H.B ≤ 2 ^ 32
  nkey : kp.toNat + kl ≤ 2 ^ 32

/-- The bodies of `init`'s loops. -/
def keyBody : List Instr :=
  [.mov .eax (.reg .esi), .alu .add .eax (.reg .ebx), .movzx8 .eax (at_ .eax 0),
    .mov .ecx (.reg .eax), .alu .xor .eax (.imm 0x36), .mov .edx (.reg .ebp), .alu .add .edx (.reg .ebx),
    .store8 (at_ .edx H.buf) .al, .alu .xor .ecx (.imm 0x5c), .store8 (at_ .edx (H.buf + H.B)) .cl,
    .alu .add .ebx (.imm 1), .alu .cmp .ebx (.reg .edi)]

def padBody : List Instr :=
  [.mov .edx (.reg .ebp), .alu .add .edx (.reg .ebx), .store8 (at_ .edx H.buf) .al,
    .store8 (at_ .edx (H.buf + H.B)) .cl, .alu .add .ebx (.imm 1),
    .alu .cmp .ebx (.imm (BitVec.ofNat 32 H.B))]

theorem keyLoop_eq : H.keyLoop = .loop (.block (keyBody H)) .ne := rfl
theorem padLoop_eq : H.padLoop = .loop (.block (padBody H)) .ne := rfl

theorem pad_byte32 (b : Byte) (v : BitVec 32) : (b.setWidth 32 ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem ipad32 : (0x36 : BitVec 32).setWidth 8 = Spec.Hmac.ipad := by decide
theorem opad32 : (0x5c : BitVec 32).setWidth 8 = Spec.Hmac.opad := by decide
theorem zero_ipad : (0x36 : BitVec 32).setWidth 8 = (0 : Byte) ^^^ Spec.Hmac.ipad := by decide
theorem zero_opad : (0x5c : BitVec 32).setWidth 8 = (0 : Byte) ^^^ Spec.Hmac.opad := by decide

theorem key_step {scr kp : BitVec 32} {kl : Nat} {s : State} (hr : LoopRegs scr kp kl s)
    (hm : LoopMem H scr kp kl s) {j : Nat} (hj : j < kl) {t : State}
    (h : KeyInv H s (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl j t) :
    WP isa (.block (keyBody H)) t fun t' =>
      KeyInv H s (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl (j + 1) t' ∧
        t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hn := hm.nscr
  have hnk := hm.nkey
  set P := scr.setWidth 64 + BitVec.ofNat 64 H.buf
  set K := kp.setWidth 64
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega_nat
  have rt := hr.keep h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.Sha256.X86.contains_offset (n := 1) (by omega_nat) (by omega_nat)) hc
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), rt.esi, h.ebx, addr3 (by omega_nat)]
        exact congrArg (· + BitVec.ofNat 64 j) (BitVec.add_zero _))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hm.key j hj) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_xori fun t₅ u₅ => wp_mov fun t₆ u₆ => wp_add fun t₇ u₇ => ?_
  have a7 : ∀ o, o + j < 2 ^ 32 - scr.toNat → t₇.ea (at_ .edx o) = scr.setWidth 64 + BitVec.ofNat 64 o +
      BitVec.ofNat 64 j := fun o ho => by
    rw [ea_at, u₇.gpr, u₆.gpr, u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.other .ebx (by decide), u₂.other .ebx (by decide), u₁.other .ebx (by decide),
      u₅.other .ebp (by decide), u₄.other .ebp (by decide), u₃.other .ebp (by decide),
      u₂.other .ebp (by decide), u₁.other .ebp (by decide), rt.ebp, h.ebx, addr3 (by omega_nat)]
  refine wp_store8 (a := P + BitVec.ofNat 64 j) (a7 _ (by omega_nat))
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega_nat)) fun t₈ m₈ => ?_
  refine wp_xori fun t₉ u₉ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [ea_at, u₉.other _ (by decide), m₈.gpr, ← ea_at, a7 _ (by omega_nat)]; simp only [P, add_ofNat_add])
    (by rw [u₉.wr, m₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]
        exact hm.buf (H.B + j) (by omega_nat))
    fun t₁₀ m₁₀ => ?_
  refine wp_addi fun t₁₁ u₁₁ => wp_cmp fun t₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_
  have k : ∀ r ∉ clob, t₁₂.gpr r = t.gpr r := fun r hr' => by
    rw [f₁₂.gpr, u₁₁.other r (nm hr' .ebx), m₁₀.gpr, u₉.other r (nm hr' .ecx), m₈.gpr,
      u₇.other r (nm hr' .edx), u₆.other r (nm hr' .edx), u₅.other r (nm hr' .eax), u₄.other r (nm hr' .ecx),
      u₃.other r (nm hr' .eax), u₂.other r (nm hr' .eax), u₁.other r (nm hr' .eax)]
  have h11 : t₁₁.gpr .ebx = BitVec.ofNat 32 (j + 1) := by
    rw [u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.ebx, ofNat_succ32]
  have hdi : t₁₁.gpr .edi = BitVec.ofNat 32 kl := by
    rw [u₁₁.other _ (by decide), m₁₀.gpr, u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), rt.edi]
  refine ⟨⟨by rw [f₁₂.rd, u₁₁.rd, m₁₀.rd, u₉.rd, m₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₁₂.wr, u₁₁.wr, m₁₀.wr, u₉.wr, m₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr' => by rw [k r hr', h.other r hr'], by rw [f₁₂.gpr, h11], ?_⟩,
    by rw [z₁₂, h11, hdi, count_z hj (by omega_nat)]⟩
  have v₁ : (t₇.gpr Reg8.al.reg).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.ipad := by
    show (t₇.gpr .eax).setWidth 8 = _
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.mem,
      u₁.mem, pad_byte32, hbyte, ipad32]
  have v₂ : (t₉.gpr Reg8.cl.reg).setWidth 8 = (K0 s.mem K kl H.B)[j] ^^^ Spec.Hmac.opad := by
    show (t₉.gpr .ecx).setWidth 8 = _
    rw [u₉.gpr, m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.gpr, u₂.mem, u₁.mem, pad_byte32, hbyte, opad32]
  rw [f₁₂.mem, u₁₁.mem, m₁₀.mem, v₂, u₉.mem, m₈.mem, v₁, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
    u₂.mem, u₁.mem]
  exact buf_write h.mem hB (by omega_nat) hl

theorem pad_step {scr kp : BitVec 32} {kl : Nat} {s₀ : State} (hr : LoopRegs scr kp kl s₀)
    (hm : LoopMem H scr kp kl s₀) {j : Nat} (hj : kl ≤ j) (hj' : j < H.B) {t : State}
    (h : KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl j t)
    (hax : t.gpr .eax = 0x36) (hcx : t.gpr .ecx = 0x5c) :
    WP isa (.block (padBody H)) t fun t' =>
      (KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl (j + 1) t' ∧
        t'.gpr .eax = 0x36 ∧ t'.gpr .ecx = 0x5c) ∧ t'.zf = some (decide (j + 1 = H.B)) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have hn := hm.nscr
  set P := scr.setWidth 64 + BitVec.ofNat 64 H.buf
  set K := kp.setWidth 64
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega_nat
  have rt := hr.keep h.other
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  have a2 : ∀ o, o + j < 2 ^ 32 - scr.toNat → t₂.ea (at_ .edx o) = scr.setWidth 64 + BitVec.ofNat 64 o +
      BitVec.ofNat 64 j := fun o ho => by
    rw [ea_at, u₂.gpr, u₁.gpr, u₁.other .ebx (by decide), rt.ebp, h.ebx, addr3 (by omega_nat)]
  refine wp_store8 (a := P + BitVec.ofNat 64 j) (a2 _ (by omega_nat))
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega_nat)) fun t₃ m₃ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [ea_at, m₃.gpr, ← ea_at, a2 _ (by omega_nat)]; simp only [P, add_ofNat_add])
    (by rw [m₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega_nat)) fun t₄ m₄ => ?_
  refine wp_addi fun t₅ u₅ => wp_cmpi fun t₆ f₆ _ z₆ => WP.block_nil ?_
  have h5 : t₅.gpr .ebx = BitVec.ofNat 32 (j + 1) := by
    rw [u₅.gpr, m₄.gpr, m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, ofNat_succ32]
  have k : ∀ r, r ≠ .edx → r ≠ .ebx → t₆.gpr r = t.gpr r := fun r h1 h2 => by
    rw [f₆.gpr, u₅.other r h2, m₄.gpr, m₃.gpr, u₂.other r h1, u₁.other r h1]
  refine ⟨⟨⟨by rw [f₆.rd, u₅.rd, m₄.rd, m₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₆.wr, u₅.wr, m₄.wr, m₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr' => by rw [k r (nm hr' .edx) (nm hr' .ebx), h.other r hr'], by rw [f₆.gpr, h5], ?_⟩,
    by rw [k _ (by decide) (by decide), hax], by rw [k _ (by decide) (by decide), hcx]⟩,
    by rw [z₆, h5, count_z hj' (by omega_nat)]⟩
  have e₁ : (t₂.gpr Reg8.al.reg).setWidth 8 = (0 : Byte) ^^^ Spec.Hmac.ipad := by
    show (t₂.gpr .eax).setWidth 8 = _
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hax, zero_ipad]
  have e₂ : (t₃.gpr Reg8.cl.reg).setWidth 8 = (0 : Byte) ^^^ Spec.Hmac.opad := by
    show (t₃.gpr .ecx).setWidth 8 = _
    rw [m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hcx, zero_opad]
  rw [f₆.mem, u₅.mem, m₄.mem, e₂, m₃.mem, e₁, u₂.mem, u₁.mem, ← K0_ge (m := s₀.mem) (K := K) (B := H.B) hj hl]
  exact buf_write h.mem hB hj' hl

theorem test_z (x : BitVec 32) : (x &&& x == 0) = decide (x.toNat = 0) := by
  rw [BitVec.and_self]
  by_cases h : x.toNat = 0
  · have : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    simp [this]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; exact h (by rw [e]; rfl)

/-- The key loop, skipped for an empty key: from `ebx = 0` and the flags of `kl = 0`. -/
theorem key_ok {scr kp : BitVec 32} {kl : Nat} {s : State} (hr : LoopRegs scr kp kl s)
    (hm : LoopMem H scr kp kl s) (hb : s.gpr .ebx = BitVec.ofNat 32 0) (hz : s.zf = some (decide (kl = 0))) :
    WP isa (.ite .e (.block []) H.keyLoop) s
      (KeyInv H s (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl kl) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  have i0 : KeyInv H s (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl 0 s :=
    ⟨rfl, rfl, fun _ _ => rfl, hb, ⟨by simp [bytesAt], by simp [bytesAt], Frame.refl _ _⟩⟩
  refine WP.ite (decide (kl = 0)) (by show eval .e s = _; rw [eval_e, hz]) (fun h0 => WP.block_nil ?_)
    fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have hpos : 0 < kl := by simp at h0; omega_nat
    rw [keyLoop_eq]
    exact count_loop hpos _ (fun k hk t h => key_step H hr hm hk h) i0

/-- The pad loop, skipped for a key of `B` bytes: from `ebx = kl`. -/
theorem pad_ok {scr kp : BitVec 32} {kl : Nat} {s₀ : State} (hr : LoopRegs scr kp kl s₀)
    (hm : LoopMem H scr kp kl s₀) {t : State}
    (h : KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl kl t) :
    WP isa (.seq (.block [.mov .eax (.imm 0x36), .mov .ecx (.imm 0x5c), .alu .cmp .ebx (.imm (BitVec.ofNat 32 H.B))])
      (.ite .e (.block []) H.padLoop)) t
      (KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl H.B) := by
  have hkl := hm.kl_le
  have hB := hm.hB
  refine WP.seq (wp_movi fun t₁ u₁ => wp_movi fun t₂ u₂ => wp_cmpi fun t₃ f₃ _ z₃ => WP.block_nil ?_)
  have i0 : KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl kl t₃ :=
    ⟨by rw [f₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₃.wr, u₂.wr, u₁.wr, h.wr],
      fun r hr' => by rw [f₃.gpr, u₂.other r (nm hr' .ecx), u₁.other r (nm hr' .eax), h.other r hr'],
      by rw [f₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx],
      by rw [f₃.mem, u₂.mem, u₁.mem]; exact h.mem⟩
  have hax : t₃.gpr .eax = 0x36 := by rw [f₃.gpr, u₂.other _ (by decide), u₁.gpr]
  have hcx : t₃.gpr .ecx = 0x5c := by rw [f₃.gpr, u₂.gpr]
  have hz : t₃.zf = some (decide (kl = H.B)) := by
    rw [z₃, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, sub_beq (by omega_nat) (by omega_nat)]
  refine WP.ite (decide (kl = H.B)) (by show eval .e t₃ = _; rw [eval_e, hz]) (fun h0 => WP.block_nil ?_)
    fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0
  · have hlt : kl < H.B := by simp at h0; omega_nat
    rw [padLoop_eq]
    have := count_loop (n := H.B - kl) (by omega_nat)
      (fun k t => KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl (kl + k) t ∧
        t.gpr .eax = 0x36 ∧ t.gpr .ecx = 0x5c)
      (fun k hk t ⟨hk', ha, hc⟩ => WP.mono (pad_step H hr hm (j := kl + k) (by omega_nat) (by omega_nat) hk' ha hc)
        fun t' ⟨⟨a, b, c⟩, d⟩ => ⟨⟨by rw [← Nat.add_assoc]; exact a, b, c⟩,
          by rw [d]; exact congrArg some (decide_eq_decide.mpr (by omega_nat))⟩)
      (s := t₃) ⟨by simpa using i0, hax, hcx⟩
    rw [show kl + (H.B - kl) = H.B by omega_nat] at this
    exact WP.mono this fun _ h => h.1

end VG.Proof.Hmac.Generic.X86

/-!
## Our caller's registers

As on the other targets
(`Proof/Hmac/Generic/Arm/Init.lean`): the callee-saved registers we use
(`ebx`, `esi`, `edi`, `ebp`) are stored in `scratch` after the working
space of the functions we call (`Hash.saved`), with `scratch` in `eax`, and
loaded back at the end, with `scratch` copied from `ebp` into `eax` first.
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_store sub_offset)
open VG.Proof.Hmac.Generic.Common (InRegions.right' add_ofNat_add)

variable (H : Hash)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.ebx, .esi, .edi, .ebp]

theorem callee_saved : ∀ r ∈ calleeSaved, r ≠ .esp → r ∈ savedRegs := by decide

/-- Where the registers are saved. -/
abbrev saveR (scr : BitVec 32) : Region := ⟨scr.setWidth 64 + BitVec.ofNat 64 (8 * H.W), 16⟩

/-- The registers of `s₀` saved in the memory `m`. -/
def SavedRegs (scr : BitVec 32) (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ H.saved, m.readW (scr.setWidth 64 + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

theorem saved_mem {p : Reg × Nat} (hp : p ∈ H.saved) : 8 * H.W ≤ p.2 ∧ p.2 + 4 ≤ 8 * H.W + 16 := by
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega_nat

theorem saved_pairwise : H.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  simp [Hash.saved]

/-- Slot `d` of the save area. -/
theorem slot_sub (scr : BitVec 32) {d : Nat} (h₁ : 8 * H.W ≤ d) (h₂ : d + 4 ≤ 8 * H.W + 16) :
    Region.Sub ⟨scr.setWidth 64 + BitVec.ofNat 64 d, 4⟩ (saveR H scr) := by
  rw [show d = 8 * H.W + (d - 8 * H.W) by omega_nat, ← add_ofNat_add]
  exact sub_offset (by omega_nat) (by omega_nat)

theorem SavedRegs.frame {scr : BitVec 32} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := fun p hp => by
  obtain ⟨h₁, h₂⟩ := saved_mem H hp
  rw [← h p hp]
  exact hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (slot_sub H scr h₁ h₂)) (by decide)

/-- The registers saved from a state that agrees on them. -/
theorem SavedRegs.of_eq {scr : BitVec 32} {s₀ s₁ : State} {m : Mem} (h : SavedRegs H scr s₁ m)
    (he : ∀ r ∈ savedRegs, s₁.gpr r = s₀.gpr r) : SavedRegs H scr s₀ m := fun p hp => by
  rw [h p hp]
  refine he _ ?_
  simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

/-- The memory after storing `g r` at `B + d` for each `(r, d)` of `l`. -/
def saveMem (m : Mem) (B : Addr) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | (r, d) :: l => saveMem (m.writeW (B + BitVec.ofNat 64 d) (g r)) B g l

theorem saveList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions s.wr ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = saveMem s.mem ((s.gpr .eax).setWidth 64) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h2⟩ := hl p (by simp)
    refine wp_store (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2)
      (by rw [ea_at, addr_eq h1]) h2 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep B h (by omega_nat) (by omega_nat)) (by decide)

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

theorem save_eq : H.save = H.saved.map (fun p => Instr.store (at_ .eax p.2) p.1) := rfl

/-- Saving the registers, with `scratch` in `eax`. -/
theorem save_ok {s : State} {scr : BitVec 32} {L : Nat} (hax : s.gpr .eax = scr) (hW : H.W ≤ 64)
    (hsc : ⟨scr.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L) (hfit : scr.toNat + L ≤ 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  rw [save_eq]
  refine saveList_ok H.saved s Q (fun p hp => ?_) fun s' g rd wr m => k s' g rd wr ?_ ?_
  · obtain ⟨h₁, h₂⟩ := saved_mem H hp
    rw [hax]
    exact ⟨by omega_nat, ⟨_, hsc, contains_offset (by omega_nat) (by omega_nat)⟩⟩
  · rw [m, hax]
    exact saveMem_frameR _ _ _ _ (by omega_nat) _ _ fun p hp => saved_mem H hp
  · intro p hp
    rw [m, hax]
    exact saveMem_read _ _ _ _ (saved_pairwise H) (fun q hq => by have := saved_mem H hq; omega_nat) p hp

theorem restoreList_ok {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ .eax ∧ (s.gpr .eax).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW ((s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_movm (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 p.2) (by rw [ea_at, addr_eq h2]) h3
      fun s₁ u₁ => ?_
    have eb : s₁.gpr .eax = s.gpr .eax := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem restore_eq :
    H.restore = .mov .eax (.reg .ebp) :: H.saved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) := rfl

theorem saved_fst : H.saved.map Prod.fst = savedRegs := rfl

/-- Loading them back, with `scratch` in `ebp`. -/
theorem restore_ok {s : State} {scr : BitVec 32} {L : Nat} (hbp : s.gpr .ebp = scr) {s₀ : State} (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr.setWidth 64, L⟩ ∈ s.wr) (hL : 8 * H.W + 16 ≤ L)
    (hfit : scr.toNat + L ≤ 2 ^ 32) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → r ≠ .eax → s'.gpr r = s.gpr r) := by
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr := by rw [u₁.gpr, hbp]
  rw [← List.append_nil (List.map _ _)]
  refine restoreList_ok H.saved s₁ _ (by rw [saved_fst]; decide) (fun p hp => ?_)
    fun s₂ hl ho hm hrd hwr => WP.block_nil ⟨by rw [hm, u₁.mem], by rw [hrd, u₁.rd], by rw [hwr, u₁.wr],
      fun r hr => ?_, fun r hr hr' => ?_⟩
  · have := saved_mem H hp
    refine ⟨?_, by rw [e₁]; omega_nat, ?_⟩
    · simp only [Hash.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
    · rw [e₁, u₁.rd, u₁.wr]; exact InRegions.right' ⟨_, hsc, contains_offset (by omega_nat) (by omega_nat)⟩
  · have hv : ∀ p ∈ H.saved, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp => by
      rw [hl p hp, e₁, u₁.mem, hs p hp]
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hv (.ebx, 8 * H.W) (by simp [Hash.saved])
    · exact hv (.esi, 8 * H.W + 4) (by simp [Hash.saved])
    · exact hv (.edi, 8 * H.W + 8) (by simp [Hash.saved])
    · exact hv (.ebp, 8 * H.W + 12) (by simp [Hash.saved])
  · rw [ho r (by rw [saved_fst]; exact hr), u₁.other r hr']

/-! ## Odds and ends -/

theorem toNat_setWidth (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_nat)

/-- `x + o`, as a register holds it, where nothing wraps around. -/
theorem setWidth_add {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 o := by
  have := addr_eq (x := x) (k := o) h
  simpa only [addr] using this

theorem toNat_add_ofNat {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_nat), Nat.mod_eq_of_lt h]

/-! ## The stack

The 48 bytes below `esp` lie below the return address and the arguments;
what does not write those leaves them, and our arguments, as on entry. -/

theorem stk_ret {E : BitVec 32} (hE : 48 ≤ E.toNat) (_hf : E.toNat + 4 ≤ 2 ^ 32) :
    (below E 48).Disjoint ⟨E.setWidth 64, 4⟩ := by
  unfold below
  rw [Taint.sub_setWidth hE]
  exact Offset.below_disjoint _ (by omega_nat)

theorem stk_args {E : BitVec 32} {n : Nat} (hE : 48 ≤ E.toNat) (hf : E.toNat + 4 + n ≤ 2 ^ 32) :
    (below E 48).Disjoint ⟨addr E 4, n⟩ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro a _ h₂; simp only [Region.Contains] at h₂; omega_nat
  unfold below
  rw [Taint.sub_setWidth hE, addr_eq (by omega_nat)]
  exact Offset.disjoint_below_above _ (by omega_nat)

/-- Argument `i` is at `4 i` bytes into the arguments. -/
theorem argAddr_eq (s : State) (i : Nat) :
    argAddr s i = (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 := rfl

theorem arg_sub {E : BitVec 32} {s : State} (hs : s.gpr .esp = E) {n i : Nat} (hi : 4 * i + 4 ≤ n)
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) : Region.Sub ⟨argAddr s i, 4⟩ ⟨addr E 4, n⟩ := by
  rw [argAddr_eq, hs, addr_eq (by omega_nat), show (E + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
    addr E (4 + 4 * i) from rfl, addr_eq (by omega_nat)]
  exact Offset.sub _ (by omega_nat) (by omega_nat)

theorem arg_contains {E : BitVec 32} {s : State} (hs : s.gpr .esp = E) {n i : Nat} (hi : 4 * i + 4 ≤ n)
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) : (⟨addr E 4, n⟩ : Region).Contains (argAddr s i) 4 := by
  rw [argAddr_eq, hs, addr_eq (by omega_nat), show (E + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 =
    addr E (4 + 4 * i) from rfl, addr_eq (by omega_nat)]
  exact Offset.contains _ (by omega_nat) (by omega_nat) (by omega_nat)

/-- The arguments are kept by what writes elsewhere. -/
theorem arg_keep {E : BitVec 32} {s₀ s : State} (h₀ : s₀.gpr .esp = E) (hs : s.gpr .esp = E) {n : Nat}
    (hf : E.toNat + 4 + n ≤ 2 ^ 32) {rs : List Region} (hm : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨addr E 4, n⟩ r) {i : Nat} (hi : 4 * i + 4 ≤ n) : arg s i = arg s₀ i := by
  simp only [arg]
  rw [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hs, h₀]]
  exact hm.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (arg_sub h₀ hi hf)) (by decide)

end VG.Proof.Hmac.Generic.X86

/-!
## `init`, correct

As on the other targets
(`Proof/Hmac/Generic/Arm/Init.lean`). The arguments are on the stack:
`scratch`, then `key` and `key_len` are loaded first (after our caller's
registers are saved in `scratch`), and `inner` and `outer` once the keys are
written. The functions we call keep `ebx`, `esi`, `edi` and `ebp`, which
hold `inner`, `outer`, the low word of `update`'s count and `scratch`.
-/

namespace VG.Proof.Hmac.Generic.X86.Init

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Hmac.Generic.X86
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_mov wp_movi wp_movm wp_add wp_addi wp_test sub_offset)
open VG.Proof.Hmac.Generic.Common (add_ofNat_add bytesAt_prefix_congr inRegions_of_sub K0 K0_length
  off_disj off_disj0 sub_of_off sub_of_self bytes_keep take_map_xor)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev out : BitVec 32 := arg s₀ 1
abbrev kp : BitVec 32 := arg s₀ 2
abbrev kl : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev inR : Region := ⟨(inn s₀).setWidth 64, H.S⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, H.S⟩
abbrev keyR : Region := ⟨(kp s₀).setWidth 64, kl s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- The padded keys. -/
abbrev P : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf
abbrev bufR : Region := ⟨P (H := H) s₀, 2 * H.B⟩
abbrev calR : Region := ⟨(scr s₀).setWidth 64, hH.Wb⟩
/-- Byte `o` of `scratch`, as a register holds it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o

end

theorem kl_lt (s₀ : State) : kl s₀ < 2 ^ 32 := (arg s₀ 3).isLt

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_o : (retR s₀).Disjoint (outR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (out s₀).toNat + H.S ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.buf + 2 * H.B ≤ 8 * sc
  hB : H.B ≤ 128
  hB0 : 0 < H.B
  hW : H.W ≤ 64
  hS : H.S ≤ 256

theorem pre_of {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.buf + 2 * H.B ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h23]; rfl
  simp only [hS, hB, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, hfit, hH.hBB, hH.hB0, hH.hW, hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) :
    Region.Sub ⟨(scr s₀).setWidth 64 + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
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
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 16) (by omega_nat) (by omega_nat)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hB
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 16) (n := 2 * H.B) (by omega_nat) (by omega_nat)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.hW; have := hp.hB
  exact off_disj _ (a := 8 * H.W) (m := 16) (b := 8 * H.W + 16) (n := 2 * H.B) (by omega_nat) (by omega_nat)
    (by omega_nat)

theorem addr_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) :
    (dO s₀ o).setWidth 64 = (scr s₀).setWidth 64 + BitVec.ofNat 64 o :=
  setWidth_add (by have := hp.nw; omega_nat)

theorem toNat_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) : (dO s₀ o).toNat = (scr s₀).toNat + o :=
  toNat_add_ofNat (by have := hp.nw; omega_nat)

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega_nat)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega_nat)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {sc : Nat}

/-- `KR` survives changes to other registers, and to memory in our buffers
(away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') : KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

/-- The arguments, while `KR` holds. -/
theorem KR.argEq {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) : VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega_nat) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega_nat)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : KR (H := H) sc s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_o
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

/-- `KR` after a call that writes `rs`, parts of our buffers. -/
theorem KR.call {s s' : State} (hk : KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [show stk s = stkR s₀ by rw [stk, hk.esp]] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (save_sub hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hsub r hr
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [ea_at, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega_nat) (by have := hp.spf; omega_nat)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

end

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem ((kp s₀).setWidth 64) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) sc s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) sc s₀) := by
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf
  have hsc : ⟨(scr s₀).setWidth 64, 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  have dA : ∀ r ∈ [saveR H (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  refine WP.seq ?_
  simp only [Hash.initPrologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (argW rfl 4) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (by omega_nat) (by omega_nat)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega_nat) (by have := hp.spf; omega_nat))) (by decide)
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 3) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl (by decide))
    fun s₅ u₅ => ?_
  refine wp_movi fun s₆ u₆ => wp_test fun s₇ f₇ z₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = s₂.mem := by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hrd : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have hwr : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have hbp : s₇.gpr .ebp = scr s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl
  have hsi : s₇.gpr .esi = kp s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 2 (by decide)]
  have hdi : s₇.gpr .edi = BitVec.ofNat 32 (kl s₀) := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 3 (by decide), BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have hbx : s₇.gpr .ebx = BitVec.ofNat 32 0 := by rw [f₇.gpr, u₆.gpr]; rfl
  have hsp : s₇.gpr .esp = E s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  have hz : s₇.zf = some (decide (kl s₀ = 0)) := by
    rw [z₇, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 3 (by decide), test_z]
  have hr : LoopRegs (scr s₀) (kp s₀) (kl s₀) s₇ := ⟨hbp, hsi, hdi⟩
  have hm : LoopMem H (scr s₀) (kp s₀) (kl s₀) s₇ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (Nat.lt_trans (kl_lt s₀) (by decide))
          hk |>.elim fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by
        rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega_nat) hk,
      hp.k_s.sub_right (buf_sub hp), hB, by simp only [Hash.buf]; omega_nat, hp.nk⟩
  refine WP.seq (WP.mono (key_ok H hr hm hbx hz) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₇.mem := by rw [hm₇]; exact f₂'
  have eK : K0 s₇.mem ((kp s₀).setWidth 64) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp)))
      (Nat.le_of_lt (Nat.lt_trans (kl_lt s₀) (by decide))) hi
  have hg : ∀ r ∉ clob, t.gpr r = s₇.gpr r := ht.other
  have sv : SavedRegs H (scr s₀) s₀ s₇.mem := hm₇ ▸ sv₂.of_eq H fun r hr => u₁.other r (by
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have ft : Frame [bufR (H := H) s₀] s₇.mem t.mem := ht.mem.frame
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [hg _ (by decide), hsp], by rw [hg _ (by decide), hbp],
    sv.frame H ft (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp),
    (fk.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩).trans
      (ft.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, buf_sub hp⟩)⟩, ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

/-- `KR`, with `inner` in `ebx` and `outer` in `esi`. -/
structure KS (s₀ s : State) : Prop extends KR (H := H) sc s₀ s where
  ebx : s.gpr .ebx = inn s₀
  esi : s.gpr .esi = out s₀

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem states_ok {s : State} (hk : KR (H := H) sc s₀ s) :
    WP isa (.block Hash.initStates) s fun t => KS (H := H) sc s₀ t ∧ t.mem = s.mem := by
  refine wp_movm (a := argAddr s₀ 0) (argW hk.esp 0) (argIn hp hk.rd hk.wr (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by rw [ea_at, u₁.other _ (by decide), hk.esp]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact argIn hp hk.rd hk.wr (by decide)) fun t₂ u₂ => WP.block_nil ?_
  exact ⟨⟨(hk.upd (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr, hk.readArg hp (by decide)],
    by rw [u₂.gpr, u₁.mem, hk.readArg hp (by decide)]⟩, by rw [u₂.mem, u₁.mem]⟩

theorem state_disj {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p.setWidth 64, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p.setWidth 64, H.S⟩ ∧
      (saveR H (scr s₀)).Disjoint ⟨p.setWidth 64, H.S⟩ ∧ p.toNat + H.S ≤ 2 ^ 32 := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (save_sub hp), hp.ni⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (save_sub hp), hp.no⟩

theorem state_in {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨p.setWidth 64, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem state_wrs {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub ⟨p.setWidth 64, H.S⟩ r' := by
  rcases hpR with rfl | rfl
  · exact ⟨inR (H := H) s₀, by simp, fun _ h => h⟩
  · exact ⟨outR (H := H) s₀, by simp, fun _ h => h⟩

omit hp in
theorem stk_eq {s : State} (hk : KR (H := H) sc s₀ s) : stk s = stkR s₀ := by rw [stk, hk.esp]

/-- `KS` after a call that writes `rs`. -/
theorem KS.call {s s' : State} (hk : KS (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KS (H := H) sc s₀ s' :=
  ⟨hk.toKR.call hp ha hs hsub, by rw [ha.cs .ebx (by simp [calleeSaved]), hk.ebx],
    by rw [ha.cs .esi (by simp [calleeSaved]), hk.esi]⟩

theorem callInit_ok {s : State} (hk : KS (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KS (H := H) sc s₀ s' → Frame [⟨p.setWidth 64, H.S⟩, stkR s₀] s.mem s'.mem →
      hH.SH.Repr s'.mem (p.setWidth 64) [] → Q s') :
    WP isa (H.callInit st) s Q := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨dS, dK, dV, np⟩ := state_disj hp hpR
  have hsp := hk.esp
  refine init_frame hH (st := p)
    { hst := by rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hk.ebx, hk.esi]
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      sp48 := by rw [hsp]; exact hp.sp48
      cw := by rw [hk.wr]; exact covers_one (state_in hp hpR)
      b_st := by rw [stk_eq hk.toKR]; exact dK
      nst := np } fun s' ha hr => ?_
  have f := ha.frame
  rw [stk_eq hk.toKR] at f
  exact hQ s' (hk.call hp ha (by simp only [List.mem_singleton]; rintro r rfl; exact dV)
    (by simp only [List.mem_singleton]; rintro r rfl; exact state_wrs hpR)) f hr

/-- The block before `update`'s frame, from `st` at offset `o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  [] ++ ([.mov .eax (.imm 0), .mov .edi (.imm (BitVec.ofNat 32 0)), .mov .ecx (.imm (BitVec.ofNat 32 H.B))] : List Instr) ++
    Impl.Hmac.Generic.X86.scr .edx o

theorem updArgs_ok {s : State} (hk : KS (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block (updBlock H o)) s fun t =>
      KS (H := H) sc s₀ t ∧ UpdArgs hH t .edi st p (dO s₀ o) (scr s₀) (BitVec.ofNat 32 0) H.B ∧ t.mem = s.mem := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨dS, dK, dV, np⟩ := state_disj hp hpR
  have hB := hp.hB; have hB0 := hp.hB0; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o + H.B ≤ 8 * sc := by omega_nat
  have ea := addr_dO hp (o := o) (by omega_nat)
  have dsub : Region.Sub ⟨(dO s₀ o).setWidth 64, H.B⟩ (bufR (H := H) s₀) := by
    rw [ea]
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨(dO s₀ o).setWidth 64, H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  simp only [updBlock, Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addi fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → r ≠ .edx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have k₅ : KS (H := H) sc s₀ s₅ :=
    ⟨((((hk.toKR.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅, by rw [g _ (by decide) (by decide) (by decide) (by decide), hk.ebx],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), hk.esi]⟩
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₅, ?_, hm⟩
  exact
    { hst := by
        rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact k₅.ebx
        · exact k₅.esi
      hlo := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
      eax := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.gpr]
      ecx := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
      edx := by rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
          hk.ebp]
      ebp := k₅.ebp
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      hl := by decide
      hlen := by omega_nat
      sp48 := by rw [k₅.esp]; exact hp.sp48
      cd := by
        rw [k₅.rd, k₅.wr, ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.rd, hp.wr]; simp) ho'
      cw := by
        rw [k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨p.setWidth 64, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega_nat)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      b_st := by rw [stk_eq k₅.toKR]; exact dK
      b_d := by rw [stk_eq k₅.toKR]; exact hp.b_s.sub_right dsc
      b_sc := by rw [stk_eq k₅.toKR]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := np
      nd := by rw [toNat_dO hp (by omega_nat)]; omega_nat
      nsc := by have := hH.hWb; omega_nat }

theorem updCall_ok {t : State} (hk : KS (H := H) sc s₀ t) {st : Reg} {p d : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (ha : UpdArgs hH t .edi st p d (scr s₀) (BitVec.ofNat 32 0) H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KS (H := H) sc s₀ s' → Frame [⟨p.setWidth 64, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem (p.setWidth 64) [] →
        hH.SH.Repr s'.mem (p.setWidth 64) ([] ++ bytesAt t.mem (d.setWidth 64) H.B)) → Q s') :
    WP isa (.frame (.push (upd6 .edi st)) (.call H.updN H.updC) (.pop .eax (upd6 .edi st).length)) t Q := by
  obtain ⟨dS, dK, dV, np⟩ := state_disj hp hpR
  refine upd_frame hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [stk_eq hk.toKR] at f
  refine hQ s' (hk.call hp ha' ?_ ?_) f fun hr => hpost [] hr (by rw [zero_append_ofNat (by decide)]; rfl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV
    · exact (cal_save hH hp).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact state_wrs hpR
    · exact ⟨scR sc s₀, by simp, cal_sub hH hp⟩

theorem callUpd_ok {s : State} (hk : KS (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KS (H := H) sc s₀ s' → Frame [⟨p.setWidth 64, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem (p.setWidth 64) [] →
        hH.SH.Repr s'.mem (p.setWidth 64) ([] ++ bytesAt s.mem ((scr s₀).setWidth 64 + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [] st .edi 0 o H.B) s Q := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hf := hp.fits; have := hp.hB; have := hp.hB0; have ho' := ho; simp only [Hash.buf] at hf ho'
  have ea := addr_dO hp (o := o) (by omega_nat)
  refine WP.seq (WP.mono (updArgs_ok hH hp hk hst ho) fun t ⟨k, a, m⟩ =>
    updCall_ok hH hp k hpR a fun s' k' f r => hQ s' k' (m ▸ f) fun hr => ?_)
  have := r (m ▸ hr)
  rwa [m, ea] at this

/-! ## Correctness -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

include hH in
theorem blockKey_eq :
    blockKey hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.Common.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega_nat,
    ↓reduceIte]

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
  have eO : (scr s₀).setWidth 64 + BitVec.ofNat 64 (H.buf + H.B) = P (H := H) s₀ + BitVec.ofNat 64 H.B := by
    rw [P, add_ofNat_add]
  refine WP.seq (WP.mono (keys_ok sc hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (states_ok hp h₁.kr) fun s₂ ⟨k₂, m₂⟩ => ?_)
  have bI₂ : bytesAt s₂.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad := by rw [m₂]; exact h₁.bufI
  have bO₂ : bytesAt s₂.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad := by
    rw [m₂]; exact h₁.bufO
  refine WP.seq (callInit_ok hH hp k₂ (.inl ⟨rfl, rfl⟩) fun s₃ k₃ f₃ r₃ => ?_)
  have bI₃ := (bytes_keep f₃ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) ; exacts [dIS, dIK])
    (by omega_nat)).trans bI₂
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) ; exacts [dOS, dOK])
    (by omega_nat)).trans bO₂
  refine WP.seq (callUpd_ok hH hp k₃ (.inl ⟨rfl, rfl⟩) (.inl rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := r₄ r₃
  rw [List.nil_append, show (scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf = P (H := H) s₀ from rfl, bI₃] at rI₄
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) ; exacts [dOS, dOC, dOK])
    (by omega_nat)).trans bO₃
  refine WP.seq (callInit_ok hH hp k₄ (.inr ⟨rfl, rfl⟩) fun s₅ k₅ f₅ r₅ => ?_)
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.b_i.symm) rI₄
  have bO₅ := (bytes_keep f₅ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) ; exacts [dOO, dOK])
    (by omega_nat)).trans bO₄
  refine WP.seq (callUpd_ok hH hp k₅ (.inr ⟨rfl, rfl⟩) (.inr rfl) fun s₆ k₆ f₆ r₆ => ?_)
  have rO₆ := r₆ r₅
  rw [List.nil_append, eO, bO₅] at rO₆
  have rI₆ := repr_keep hH f₆ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.b_i.symm) rI₅
  have hsc : ⟨(scr s₀).setWidth 64, 8 * sc⟩ ∈ s₆.wr := by rw [k₆.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₆.ebp k₆.saved hsc (by omega_nat) hp.nw) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hm]; exact k₆.toKR.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₆.esp]
    · exact hg r (callee_saved r hr he)
  · show hH.SH.Repr s'.mem ((inn s₀).setWidth 64) _ ∧ hH.SH.Repr s'.mem ((out s₀).setWidth 64) _
    rw [hm, blockKey_eq hH hp]
    exact ⟨rI₆, rO₆⟩

end

end VG.Proof.Hmac.Generic.X86.Init
