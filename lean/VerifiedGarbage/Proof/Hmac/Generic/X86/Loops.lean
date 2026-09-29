import VerifiedGarbage.Proof.Hmac.Generic.X86.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# HMAC over any streaming hash function on x86 (32-bit): the byte loops

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Hmac/Generic/Arm/Loops.lean`, whose byte-list lemmas from x86-64
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
  rw [VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega), add_ofNat_add, Nat.add_comm]

/-- The flags after counting up to `k + 1 ≤ n`. -/
theorem count_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (k + 1) - BitVec.ofNat 32 n == 0) = decide (k + 1 = n) :=
  sub_beq (by omega) hn

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
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

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
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.other src hs, h.ecx, addr3 (by omega)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_at, u₅.gpr, u₄.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), u₃.other _ (nm hd .edx), u₂.other _ (nm hd .eax),
      u₁.other _ (nm hd .eax), h.other dst hd, h.ecx, addr3 (by omega)])
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
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega)
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
    rw [h.mem]; simp only [writeBytes, hl', not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
  have rT : t.mem (T + BitVec.ofNat 64 k) = s.mem (T + BitVec.ofNat 64 k) := by
    rw [h.mem]
    simp only [writeBytes, hl', show T + BitVec.ofNat 64 k - T = BitVec.ofNat 64 k by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.lt_irrefl, ↓reduceIte]
  have gb := h.other .ebp (by decide)
  have gs := h.other .esi (by decide)
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := U + BitVec.ofNat 64 k)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), gb, h.ecx, addr3 (by omega)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hinU k hk) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  have a₅ : t₅.ea (at_ .eax 0) = T + BitVec.ofNat 64 k := by
    rw [ea_at, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gs, h.ecx,
      addr3 (by omega)]
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
      (s.mem (T + BitVec.ofNat 64 k) ^^^ s.mem (U + BitVec.ofNat 64 k)) (by rw [hl']; omega)
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
  have hl : j < (K0 s.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep h.other
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = (K0 s.mem K kl H.B)[j] := by
    rw [K0_lt hj hl]
    refine h.mem.frame _ fun r hr' hc => ?_
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hm.disj _ (Proof.Sha256.X86.contains_offset (n := 1) (by omega) (by omega)) hc
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), rt.esi, h.ebx, addr3 (by omega)]
        exact congrArg (· + BitVec.ofNat 64 j) (BitVec.add_zero _))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hm.key j hj) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_xori fun t₅ u₅ => wp_mov fun t₆ u₆ => wp_add fun t₇ u₇ => ?_
  have a7 : ∀ o, o + j < 2 ^ 32 - scr.toNat → t₇.ea (at_ .edx o) = scr.setWidth 64 + BitVec.ofNat 64 o +
      BitVec.ofNat 64 j := fun o ho => by
    rw [ea_at, u₇.gpr, u₆.gpr, u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.other .ebx (by decide), u₂.other .ebx (by decide), u₁.other .ebx (by decide),
      u₅.other .ebp (by decide), u₄.other .ebp (by decide), u₃.other .ebp (by decide),
      u₂.other .ebp (by decide), u₁.other .ebp (by decide), rt.ebp, h.ebx, addr3 (by omega)]
  refine wp_store8 (a := P + BitVec.ofNat 64 j) (a7 _ (by omega))
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₈ m₈ => ?_
  refine wp_xori fun t₉ u₉ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [ea_at, u₉.other _ (by decide), m₈.gpr, ← ea_at, a7 _ (by omega)]; simp only [P, add_ofNat_add])
    (by rw [u₉.wr, m₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]
        exact hm.buf (H.B + j) (by omega))
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
    by rw [z₁₂, h11, hdi, count_z hj (by omega)]⟩
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
  exact buf_write h.mem hB (by omega) hl

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
  have hl : j < (K0 s₀.mem K kl H.B).length := by rw [K0_length _ _ hkl]; omega
  have rt := hr.keep h.other
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  have a2 : ∀ o, o + j < 2 ^ 32 - scr.toNat → t₂.ea (at_ .edx o) = scr.setWidth 64 + BitVec.ofNat 64 o +
      BitVec.ofNat 64 j := fun o ho => by
    rw [ea_at, u₂.gpr, u₁.gpr, u₁.other .ebx (by decide), rt.ebp, h.ebx, addr3 (by omega)]
  refine wp_store8 (a := P + BitVec.ofNat 64 j) (a2 _ (by omega))
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hm.buf j (by omega)) fun t₃ m₃ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 H.B + BitVec.ofNat 64 j)
    (by rw [ea_at, m₃.gpr, ← ea_at, a2 _ (by omega)]; simp only [P, add_ofNat_add])
    (by rw [m₃.wr, u₂.wr, u₁.wr, h.wr, add_ofNat_add]; exact hm.buf (H.B + j) (by omega)) fun t₄ m₄ => ?_
  refine wp_addi fun t₅ u₅ => wp_cmpi fun t₆ f₆ _ z₆ => WP.block_nil ?_
  have h5 : t₅.gpr .ebx = BitVec.ofNat 32 (j + 1) := by
    rw [u₅.gpr, m₄.gpr, m₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, ofNat_succ32]
  have k : ∀ r, r ≠ .edx → r ≠ .ebx → t₆.gpr r = t.gpr r := fun r h1 h2 => by
    rw [f₆.gpr, u₅.other r h2, m₄.gpr, m₃.gpr, u₂.other r h1, u₁.other r h1]
  refine ⟨⟨⟨by rw [f₆.rd, u₅.rd, m₄.rd, m₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₆.wr, u₅.wr, m₄.wr, m₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr' => by rw [k r (nm hr' .edx) (nm hr' .ebx), h.other r hr'], by rw [f₆.gpr, h5], ?_⟩,
    by rw [k _ (by decide) (by decide), hax], by rw [k _ (by decide) (by decide), hcx]⟩,
    by rw [z₆, h5, count_z hj' (by omega)]⟩
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
  · have hpos : 0 < kl := by simp at h0; omega
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
    rw [z₃, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, sub_beq (by omega) (by omega)]
  refine WP.ite (decide (kl = H.B)) (by show eval .e t₃ = _; rw [eval_e, hz]) (fun h0 => WP.block_nil ?_)
    fun h0 => ?_
  · have : kl = H.B := by simpa using h0
    exact this ▸ i0
  · have hlt : kl < H.B := by simp at h0; omega
    rw [padLoop_eq]
    have := count_loop (n := H.B - kl) (by omega)
      (fun k t => KeyInv H s₀ (scr.setWidth 64 + BitVec.ofNat 64 H.buf) (kp.setWidth 64) kl (kl + k) t ∧
        t.gpr .eax = 0x36 ∧ t.gpr .ecx = 0x5c)
      (fun k hk t ⟨hk', ha, hc⟩ => WP.mono (pad_step H hr hm (j := kl + k) (by omega) (by omega) hk' ha hc)
        fun t' ⟨⟨a, b, c⟩, d⟩ => ⟨⟨by rw [← Nat.add_assoc]; exact a, b, c⟩,
          by rw [d]; exact congrArg some (decide_eq_decide.mpr (by omega))⟩)
      (s := t₃) ⟨by simpa using i0, hax, hcx⟩
    rw [show kl + (H.B - kl) = H.B by omega] at this
    exact WP.mono this fun _ h => h.1

end VG.Proof.Hmac.Generic.X86
