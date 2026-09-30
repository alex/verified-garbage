import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Blake2.AArch64.Contract
import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Impl.Blake2.AArch64.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming BLAKE2 on AArch64: common lemmas

Untrusted: everything here is checked by Lean. The contracts the proofs of
`init`, `update` and `finalize` are written against, what they need of the
compression function they call (`CalleeOk`), the call (`compressWith_ok`),
and the loops copying bytes into the buffer and zeroing it.
-/

namespace VG.Proof.Blake2

open VG.AArch64 VG.Spec.Blake2

section
variable {w : Nat} (P : Params w)

/-- AArch64 contract for `init(state = x0, outlen = x1, key = x2, keylen =
x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, bufOff w + blockBytes w⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧
    1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ P.maxBytes ∧ (s.gpr .x3).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .x1).toNat (s.gpr .x3).toNat) s'.mem
    (s.gpr .x0) (keyBlock w (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- AArch64 contract for `update(state = x0, count = x1, data = x2, len = x3,
scratch = x4)`. -/
def updateAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, bufOff w + blockBytes w⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 576⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .x0) d →
    s.gpr .x1 = BitVec.ofNat 64 d.length → d.length + (s.gpr .x3).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (s.gpr .x0) (d ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- AArch64 contract for `finalize(state = x0, count = x1, out = x2, scratch =
x3)`. -/
def finalizeAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, bufOff w + blockBytes w⟩
    let out : Region := ⟨s.gpr .x2, bufOff w⟩
    let scratch : Region := ⟨s.gpr .x3, 576⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (s.gpr .x0) d → d.length < 2 ^ 64 →
    s.gpr .x1 = BitVec.ofNat 64 d.length → bytesAt s'.mem (s.gpr .x2) (bufOff w) = finalHash P h0 d
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end

namespace AArch64.Stream

open VG.Impl.Blake2.AArch64.Stream (N B mov copyLoop zeroLoop compressWith saved save restore)
open VG.Impl.Blake2.AArch64 (lbb compress)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_addImm wp_subImm wp_movz wp_add wp_sub
  wp_and wp_lsr wp_ldrb wp_strb wp_str wp_ldr eval_zero eval_nonzero ofNat_succ ofNat_pred ofNat_beq_zero)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : Params w}

/-! ## Sizes -/

/-- The word sizes, and keys fitting a block. -/
structure Ok (P : Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N (h : Ok P) : bufOff w = blockBytes w / 2 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

/-- The sizes, all small. -/
theorem Ok.len (h : Ok P) : bufOff w + blockBytes w ≤ 192 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.N64 (h : Ok P) : bufOff w ≤ 64 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.lbb (h : Ok P) : lbb w < 64 ∧ 2 ^ lbb w = blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : N w = bufOff w := rfl
theorem B_eq : B w = blockBytes w := rfl

/-- `x >>> lbb`: division by the block size. -/
theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> lbb w = BitVec.ofNat 64 (m / blockBytes w) := by
  obtain ⟨-, lgB⟩ := hP.lbb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- `x & (B - 1)`: the remainder modulo the block size. -/
theorem mask_mod (hP : Ok P) (x : BitVec 64) :
    x &&& (BitVec.ofNat 16 (B w - 1)).setWidth 64 = BitVec.ofNat 64 (x.toNat % blockBytes w) := by
  apply BitVec.eq_of_toNat_eq
  rcases hP.w with rfl | rfl
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat,
      show ((BitVec.ofNat 16 (B 64 - 1)).setWidth 64).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 64 = 2 ^ 7 from rfl]
    omega
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat,
      show ((BitVec.ofNat 16 (B 32 - 1)).setWidth 64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 32 = 2 ^ 6 from rfl]
    omega

theorem movz_B (hP : Ok P) : (BitVec.ofNat 16 (B w)).setWidth 64 = BitVec.ofNat 64 (blockBytes w) := by
  rcases hP.w with rfl | rfl <;> rfl

theorem movz_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) :=
  MdStream.AArch64.sub_ofNat h

/-! ## The compression function -/

/-- What the calls need of the compression function: its contract, and that it
pushes no frames. -/
structure CalleeOk (P : Params w) (code : Prog isa) : Prop where
  verified : ∀ s, (compressAArch64 P).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressAArch64 P).post s s'
  noFrames : code.noFrames = true

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

/-- What the call of the compression function needs of the state `s` before
the argument set-up: the hash value `st` at `x19`, the scratch space `scr` at
`x20` and the `len` bytes of blocks at `src` do not overlap each other, and
may be accessed. -/
structure CallOk (s : State) (st scr src : Addr) (len : Nat) : Prop where
  x19 : s.gpr .x19 = st
  x20 : s.gpr .x20 = scr
  d₁ : Region.Disjoint ⟨st, bufOff w⟩ ⟨scr, 512⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, bufOff w⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, 512⟩
  hc : Covers [⟨src, len⟩, ⟨st, bufOff w⟩, ⟨scr, 512⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, bufOff w⟩, ⟨scr, 512⟩] s.wr

/-- The arguments of the call, set up from `σ`. -/
structure Setup (σ s : State) (src n t : BitVec 64) (last : Bool) : Prop where
  x0 : s.gpr .x0 = σ.gpr .x19
  x1 : s.gpr .x1 = src
  x2 : s.gpr .x2 = n
  x3 : s.gpr .x3 = t
  x4 : ((s.gpr .x4).setWidth 32 != 0) = last
  x5 : s.gpr .x5 = σ.gpr .x20
  cs : ∀ r ∈ preserved, s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- Compressing the `n` blocks at `src` into the hash value at `x19`, with
scratch space at `x20`, by calling the compression function, after `args`
set up its arguments. -/
theorem compressWith_ok {args : List Instr} (hf : CalleeOk P (compress P)) {s : State}
    {st scr src : Addr} {n t : BitVec 64} {last : Bool}
    (hs : WP isa (.block (([mov .x0 .x19] : List Instr) ++ args ++ ([mov .x5 .x20] : List Instr))) s
      fun s' => Setup s s' src n t last)
    (h : CallOk (w := w) s st scr src (blockBytes w * n.toNat))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨st, bufOff w⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt w s'.mem st = compressBlocks P (stateAt w s.mem st) s.mem src n.toNat t.toNat last →
      Q s') :
    WP isa (compressWith P args) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono hs fun s₁ hs => ?_)
  have e0 : s₁.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans (hs.x0.trans h.x19)
  have e1 : s₁.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans hs.x1
  have e2 : s₁.callEntry.gpr .x2 = n := (State.callEntry_gpr _ (by decide)).trans hs.x2
  have e3 : s₁.callEntry.gpr .x3 = t := (State.callEntry_gpr _ (by decide)).trans hs.x3
  have e4 : s₁.callEntry.gpr .x4 = s₁.gpr .x4 := State.callEntry_gpr _ (by decide)
  have e5 : s₁.callEntry.gpr .x5 = scr := (State.callEntry_gpr _ (by decide)).trans (hs.x5.trans h.x20)
  refine WP.call (k := compressAArch64 P) hf.verified
    (rd := [⟨src, blockBytes w * n.toNat⟩]) (wr := [⟨st, bufOff w⟩, ⟨scr, 512⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [compressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, e0, e1, e2, e5]
    exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw
  · intro s' hrd hwr hsp hfr hcs _ hpost
    simp only [compressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, e0, e1, e2, e3, e4, hs.x4, hs.mem] at hpost
    exact hQ s' (hrd.trans hs.rd) (hwr.trans hs.wr) (hsp.trans hs.sp)
      (fun r hr h30 => (hcs r hr h30).trans (hs.cs r hr)) (hs.mem ▸ hfr) hpost

/-! ## Copying bytes into the buffer -/

/-- The copy loop's state after `j` of `k` bytes, from `s₀`. -/
structure CopyI (s₀ : State) (dst src : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  x21 : s.gpr .x21 = src + BitVec.ofNat 64 j
  x23 : s.gpr .x23 = BitVec.ofNat 64 (r + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  ext i hi; simp

theorem nonzero_iff (s : State) {k : Nat} (h : s.gpr .x11 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    isa.eval (.nonzero .x .x11) s = some (decide (k ≠ 0)) := by
  show VG.AArch64.eval (.nonzero .x .x11) s = _
  rw [eval_nonzero, h, bne, ofNat_beq_zero hk]
  simp

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

/-- The loop copying `k ≥ 1` bytes from `src` (at `x21`) to the buffer, from
byte `r` on (in `x23`). -/
theorem copyLoop_ok {s₀ : State} {st src : Addr} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hk' : r + k < 2 ^ 32)
    (hx19 : s₀.gpr .x19 = st) (hx21 : s₀.gpr .x21 = src) (hx23 : s₀.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s₀.gpr .x11 = BitVec.ofNat 64 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨src, k⟩ ⟨st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hx21],
      by rw [hx23, Nat.add_zero], by rw [hx11, Nat.sub_zero], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega))).bytes (R := ⟨src, k⟩)
      (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  -- The byte written.
  have hout : InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hx19' : s.gpr .x19 = st := by
    rw [h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide), hx19]
  refine wp_ldrb (a := src + BitVec.ofNat 64 j) (by decide) (by rw [h.x21]; simp) hin fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_strb (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hx19', h.x23, N_eq]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
    wp_subImm (by decide) fun s₆ u₆ => WP.block_nil ?_
  have hx11' : s₆.gpr .x11 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x11, sub_ofNat (by omega), Nat.sub_sub]
  have hI : CopyI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₆ := by
    refine ⟨by omega, ?_, ?_, hx11', fun x h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₆.other x h5, u₅.other x h4, u₄.other x h3, g₃.gpr, u₂.other x h2, u₁.other x h1,
        h.other x h1 h2 h3 h4 h5]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₀.mem src k).length := by simp [bytesAt]; omega
      have hl : (List.take j (bytesAt s₀.mem src k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [nonzero_iff s₆ hx11' (by omega)]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [nonzero_iff s₆ hx11' (by omega)]; simp; omega,
      k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Zeroing the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (r + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (k - j)
  other : ∀ x, x ≠ .x12 → x ≠ .x23 → x ≠ .x11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer, from byte `r` on (in `x23`). -/
theorem zeroLoop_ok {s₀ : State} {st : Addr} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hk' : r + k < 2 ^ 32)
    (hx19 : s₀.gpr .x19 = st) (hx23 : s₀.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s₀.gpr .x11 = BitVec.ofNat 64 k) (hx9 : s₀.gpr .x9 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by rw [hx23, Nat.add_zero], by rw [hx11, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hx19' : s.gpr .x19 = st := by rw [h.other .x19 (by decide) (by decide) (by decide), hx19]
  refine wp_add fun s₁ u₁ => wp_strb (a := st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19', h.x23, N_eq]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addImm (by decide) fun s₃ u₃ => wp_subImm (by decide) fun s₄ u₄ => WP.block_nil ?_
  have hx11' : s₄.gpr .x11 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x11, sub_ofNat (by omega),
      Nat.sub_sub]
  have hI : ZI s₀ (st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hx11', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add,
        Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .x9 (by decide) (by decide) (by decide), hx9, h.mem,
        List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [nonzero_iff s₄ hx11' (by omega)]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [nonzero_iff s₄ hx11' (by omega)]; simp; omega,
      k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Saving and restoring the caller's registers -/

/-- The caller's callee-saved registers `g` are saved in the scratch space at `b`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The memory after saving `x19`–`x24` (values `g`) at `b + 512 …`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 512) (g .x19)).writeW (b + BitVec.ofNat 64 520) (g .x20)).writeW
    (b + BitVec.ofNat 64 528) (g .x21)).writeW (b + BitVec.ofNat 64 536) (g .x22)).writeW
    (b + BitVec.ofNat 64 544) (g .x23)).writeW (b + BitVec.ofNat 64 552) (g .x24)

theorem save_eq' (b : Reg) : save b = [.str .x .x19 b 512, .str .x .x20 b 520,
    .str .x .x21 b 528, .str .x .x22 b 536, .str .x .x23 b 544, .str .x .x24 b 552] := rfl

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Saved b g (saveMem m b g) := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saveMem, Mem.readW_writeW_self64, MdStream.AArch64.readW_writeW_save]

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 512, 48⟩] m (saveMem m b g) := by
  have c : ∀ d : Nat, d + 8 ≤ 48 →
      (⟨b + BitVec.ofNat 64 512, 48⟩ : Region).Contains (b + BitVec.ofNat 64 (512 + d)) (64 / 8) :=
    fun d hd => Offset.contains (k := 48) _ (by omega) (by omega) (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 8 (by omega))).writeW (List.mem_singleton_self _) _
    (c 16 (by omega))).writeW (List.mem_singleton_self _) _ (c 24 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 32 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 40 (by omega))

/-- Saving `x19`–`x24` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMem s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  rw [save_eq']
  simp only [List.cons_append, List.nil_append]
  refine wp_str (by decide) rfl (hin _ (by omega) (by omega)) fun s₁ g₁ => ?_
  refine wp_str (by decide) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin _ (by omega) (by omega))
    fun s₂ g₂ => ?_
  refine wp_str (by decide) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ g₃ => ?_
  refine wp_str (by decide) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₄ g₄ => ?_
  refine wp_str (by decide) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₅ g₅ => ?_
  refine wp_str (by decide) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₆ g₆ => ?_
  refine k s₆ (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp]) ?_
  rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  simp only [saveMem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]

/-- Restoring `x19`–`x24` from the save area at `scr`. -/
theorem restore_ok {s : State} {scr : Addr} (h20 : s.gpr .x20 = scr)
    (hin : ∀ d, 512 ≤ d → d + 8 ≤ 560 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : Saved scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  have v : ∀ r d, (r, d) ∈ saved → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  unfold restore
  refine wp_ldr (by decide) (by rw [h20]) (hin _ (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by decide) (by rw [u₁.other _ (by decide), h20])
    (by rw [u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₂ u₂ => ?_
  refine wp_ldr (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_ldr (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h20])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine wp_ldr (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin _ (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .x19 _ (by simp [saved])]
    · rw [u₆.gpr, m5, v .x20 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .x21 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .x22 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .x23 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .x24 _ (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
abbrev untouched : List Reg := [.x25, .x26, .x27, .x28, .x29]

theorem notU {r : Reg} (hr : r ∈ untouched) (x : Reg) (hx : x ∉ untouched := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

/-- The callee-saved registers but `x30` are the caller's again once `restore`
has run and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r := by
  intro r hr h30
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.x19, 512) (by simp [saved])
  · exact hsv (.x20, 520) (by simp [saved])
  · exact hsv (.x21, 528) (by simp [saved])
  · exact hsv (.x22, 536) (by simp [saved])
  · exact hsv (.x23, 544) (by simp [saved])
  · exact hsv (.x24, 552) (by simp [saved])
  all_goals first | exact absurd rfl h30 | exact hu _ (by simp [untouched])

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  MdStream.AArch64.write_frame_bytes hd hR hi

/-! ## Branches, the number of buffered bytes, and the buffer's arguments -/

theorem zero_iff (s : State) {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    isa.eval (.zero .x r) s = some (decide (k = 0)) := by
  show VG.AArch64.eval (.zero .x r) s = _
  rw [eval_zero, h, ofNat_beq_zero hk]

theorem bufLen_ok (hP : Ok P) {s : State} :
    WP isa (Impl.Blake2.AArch64.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 (Blake2.bufLen w (s.gpr .x24).toNat) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold Impl.Blake2.AArch64.Stream.bufLen
  have hn := (s.gpr .x24).isLt
  generalize hn' : (s.gpr .x24).toNat = n at hn
  have hx24 : s.gpr .x24 = BitVec.ofNat 64 n := by rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_and fun s₃ u₃ =>
    wp_addImm (by decide) fun s₄ u₄ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .x9 → r ≠ .x23 → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₄.other r h2, u₃.other r h2, u₂.other r h1, u₁.other r h2]
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hsp : s₄.sp = s.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (decide (n = 0)) (zero_iff s₄ (by rw [g _ (by decide) (by decide), hx24]) hn)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movz fun s₅ u₅ => WP.block_nil ⟨?_, fun r h1 h2 => by rw [u₅.other r h2, g r h1 h2],
      by rw [u₅.mem, hm], by rw [u₅.rd, hrd], by rw [u₅.wr, hwr], by rw [u₅.sp, hsp]⟩
    rw [u₅.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr, hsp⟩
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, hx24, sub_ofNat (by omega), mask_mod hP,
      toNat_ofNat_lt (by omega), ← BitVec.ofNat_add]
    simp only [Blake2.bufLen, hb, ↓reduceIte]

/-- The arguments for compressing the buffer, with the byte count in `x24` as
the counter and the final block flag `imm`. -/
theorem bufArgs_ok {σ : State} {imm : BitVec 16} (hN : bufOff w < 4096) :
    WP isa (.block (([mov .x0 .x19] : List Instr) ++ ([.addImm .x .x1 .x19 (N w), .movz .x .x2 1 0,
      mov .x3 .x24, .movz .x .x4 imm 0] : List Instr) ++ ([mov .x5 .x20] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .x19 + BitVec.ofNat 64 (bufOff w)) (BitVec.setWidth 64 (1 : BitVec 16))
        (σ.gpr .x24) ((imm.setWidth 64).setWidth 32 != 0) := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addImm hN fun s₂ u₂ => wp_movz fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  have hcs : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), N_eq]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  have hN := hP.len
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

end AArch64.Stream

end VG.Proof.Blake2
