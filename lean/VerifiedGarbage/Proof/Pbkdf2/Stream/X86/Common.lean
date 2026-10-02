import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Calls of a streaming hash function on x86 (32-bit): byte loops, registers, stack

The byte loops, our caller's registers and the stack, which HMAC's `init` and
`finalize`, PBKDF2's `iterate` (`Proof/Pbkdf2/Md/X86/`) and the whole of
PBKDF2 (`Proof/Pbkdf2/Whole/X86/`) share.
-/

/-!
## The byte loops

As on the other targets
(`Proof/Pbkdf2/Stream/Arm/Common.lean`, whose byte-list lemmas from x86-64
are reused): the byte copy (`copy`) and the exclusive-or of `U` into `T`.
Each counts an index up from 0 and compares it with its bound. The model has no index registers,
so each access computes its address first: byte `k` of a buffer at
`p + o` is at `[x + o]` with `x = p + k`, which is `p + o + k`, as nothing
wraps around the 32-bit address space.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash copy at_)
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

/-- The zero flag of `test x, x`. -/
theorem test_z (x : BitVec 32) : (x &&& x == 0) = decide (x.toNat = 0) := by
  rw [BitVec.and_self]
  by_cases h : x.toNat = 0
  · have : x = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    simp [this]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; exact h (by rw [e]; rfl)

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

end VG.Proof.Pbkdf2.Stream.X86

/-!
## Our caller's registers

As on the other targets
(`Proof/Pbkdf2/Stream/Arm/Common.lean`): the callee-saved registers we use
(`ebx`, `esi`, `edi`, `ebp`) are stored in `scratch` after the working
space of the functions we call (`Hash.saved`), with `scratch` in `eax`, and
loaded back at the end, with `scratch` copied from `ebp` into `eax` first.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_)
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

/-- Where argument `i` is read, while `esp` is as on entry. -/
theorem argW {s₀ s : State} (hs : s.gpr .esp = s₀.gpr .esp) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [ea_at, hs]; rfl

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

/-- A streaming state is kept by what writes elsewhere. -/
theorem repr_keep {H : Hash} (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

end VG.Proof.Pbkdf2.Stream.X86
