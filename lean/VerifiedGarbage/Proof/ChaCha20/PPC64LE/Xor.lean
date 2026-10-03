import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Xor
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import Mathlib.Tactic.Conv

/-!
# ChaCha20 keystream XOR on PPC64LE

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.ChaCha20.AArch64.Xor`).
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.PPC64LE

/-- The contract the proof is written against; the artifact's is the shared
contract of `Spec/`, which implies it.
PPC64LE contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other; `data` does not wrap around the end of the
address space. The return address is in the link register, and the code
uses no stack. The pointers and the length are public; the state and the
data are secret. -/
def xorPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 64⟩
    let data : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let buf : Region := ⟨s.gpr .r6, 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
        (keystream (stateAt s.mem (s.gpr .r3)) (s.gpr .r5).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.PPC64LE.Xor

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE.Xor
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor
  serialize_stateAt)
open VG.Proof.ChaCha20.PPC64LE (toNat_ofNat_lt contains_off readW_writeW_out block_verified)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  lr : s'.lr = s.lr

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addi hn (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem wp_mflr {d : Reg} (k : ∀ s', Upd s s' d s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _))

theorem wp_mtlr {r : Reg}
    (k : ∀ s', Mupd s s' s.mem → s'.lr = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read_one]

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem wp_stw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w hn ho (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wp_lwz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w hn ho (by rw [ha]; exact hin), ha]

end

/-- Registers that code never writes keep their values. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-! ## Arithmetic -/

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- `x >>> 6`, of a number below 2⁶⁴. -/
theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 6 = BitVec.ofNat 64 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0) := by
  change VG.PPC64LE.eval (.zero .d r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  change VG.PPC64LE.eval (.nonzero .d r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

theorem eval_nonzero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.nonzero .d r) s = some (decide (k ≠ 0)) := by
  rw [eval_nonzero, h, bne, ofNat_beq_zero hk]
  simp

/-- The byte stored by `xor r6, r6, r8; stb r6, …` after two `lbz`s. -/
theorem xor_setWidth (a b : Byte) : ((a.setWidth 64 ^^^ b.setWidth 64).setWidth 8) = a ^^^ b := by
  ext i hi; simp

/-- The word stored by `addi r8, r8, 1; stw r8, …` after an `lwz r8`. -/
theorem inc_setWidth (v : BitVec 32) :
    ((v.setWidth 64 + BitVec.ofNat 64 1).setWidth 32) = v + 1 := by
  rw [lo32_add, lo32_ext]; rfl

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .r3
abbrev dp : Addr := s₀.gpr .r4
abbrev L : Nat := (s₀.gpr .r5).toNat
abbrev bp : Addr := s₀.gpr .r6
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev bR : Region := ⟨bp s₀, 320⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .r5).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, bR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_b : (stR s₀).Disjoint (bR s₀)
  d_b : (dR s₀).Disjoint (bR s₀)
  nowrap : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorPPC64LE.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Our caller's `r22` and `r23`, and our return address, saved in
`buf[256, 280)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (bp s₀ + BitVec.ofNat 64 256) 64 = s₀.gpr .r22 ∧
  m.readW (bp s₀ + BitVec.ofNat 64 264) 64 = s₀.gpr .r23 ∧
  m.readW (bp s₀ + BitVec.ofNat 64 272) 64 = s₀.lr

/-- The callee-saved registers the block function writes (and restores). -/
def nvRegs : List Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21]

/-- They hold our caller's values. -/
def NV (s₀ s : State) : Prop := ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r

/-- Before block `j` (the loop's invariant). -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = bp s₀
  r22 : s.gpr .r22 = dp s₀ + BitVec.ofNat 64 (P s₀ j)
  r23 : s.gpr .r23 = BitVec.ofNat 64 (L s₀ - P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem

/-! ## Memory -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_out m p v (j := i) (k := 12) hi (by omega) (by omega)

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_off (by omega) (by omega)) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bp s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨bp s₀ + BitVec.ofNat 64 256, 24⟩

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bR s₀) := Region.sub_prefix (by omega)

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bR s₀) := by
  intro a ha
  simp only [Region.Contains] at *
  bv_omega

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := by
  intro a h₁ h₂
  simp only [Region.Contains] at *
  bv_omega

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 256 ≤ d → d + 8 ≤ 280 → (savR s₀).Contains (bp s₀ + BitVec.ofNat 64 d) (64 / 8) := by
    intro d h₁ h₂
    simp only [Region.Contains]
    rw [show bp s₀ + BitVec.ofNat 64 d - (bp s₀ + BitVec.ofNat 64 256) = BitVec.ofNat 64 (d - 256) by
      bv_omega, toNat_ofNat_lt (by omega)]
    omega
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hf.readW (c 256 (Nat.le_refl _) (by omega)) hd (by decide), h1],
    by rw [hf.readW (c 264 (by omega) (by omega)) hd (by decide), h2],
    by rw [hf.readW (c 272 (by omega) (by omega)) hd (by decide), h3]⟩

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (fun _ _ _ => by bv_omega) (by decide)

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < L s₀) (hk' : k' < L s₀) (h : k' ≠ k) :
    dp s₀ + BitVec.ofNat 64 k' ≠ dp s₀ + BitVec.ofNat 64 k := by
  have hL := L_lt s₀
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - dp s₀) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  exact h this

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      bv_omega
    simp only [this, h, ↓reduceIte]

/-! ## The prologue -/

theorem save_eq : save ++ [mov .r22 .r4, mov .r23 .r5, mov .r4 .r6] =
    [.store .d .r22 .r6 256, .store .d .r23 .r6 264, .mflr .r0, .store .d .r0 .r6 272,
      mov .r22 .r4, mov .r23 .r5, mov .r4 .r6] := rfl

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ [mov .r22 .r4, mov .r23 .r5, mov .r4 .r6])) s₀ (OInv s₀ 0) := by
  have o : ∀ d, d + 8 ≤ 320 → InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨bR s₀, by simp [hp.wr], contains_off hd (by omega)⟩
  rw [save_eq]
  refine wp_std (a := bp s₀ + BitVec.ofNat 64 256) (by decide) (by decide) rfl (o 256 (by omega))
    fun s₁ g₁ l₁ => ?_
  refine wp_std (a := bp s₀ + BitVec.ofNat 64 264) (by decide) (by decide) (by rw [g₁.gpr])
    (by rw [g₁.wr]; exact o 264 (by omega)) fun s₂ g₂ l₂ => ?_
  refine wp_mflr fun s₃ u₃ => ?_
  refine wp_std (a := bp s₀ + BitVec.ofNat 64 272) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), g₂.gpr, g₁.gpr])
    (by rw [u₃.wr, g₂.wr, g₁.wr]; exact o 272 (by omega)) fun s₄ g₄ _ => ?_
  refine wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r0 → s₄.gpr r = s₀.gpr r := fun r h => by
    rw [g₄.gpr, u₃.other r h, g₂.gpr, g₁.gpr]
  have hm : s₇.mem = ((s₀.mem.writeW (bp s₀ + BitVec.ofNat 64 256) (s₀.gpr .r22)).writeW
      (bp s₀ + BitVec.ofNat 64 264) (s₀.gpr .r23)).writeW (bp s₀ + BitVec.ofNat 64 272) s₀.lr := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.gpr, l₂, l₁, u₃.mem, g₂.mem, g₁.gpr, g₁.mem]
  have hf : Frame [bR s₀] s₀.mem s₇.mem := by
    rw [hm]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g _ (by decide)]; simp [P]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g _ (by decide)]; simp [P]
  · rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, g₂.rd, g₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, g₂.wr, g₁.wr]
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dR s₀) (by simpa using hp.d_b) (L_lt s₀).le hk
  · rw [hm]
    refine ⟨?_, ?_, ?_⟩
    · rw [readW64_off _ _ _ (by omega) (by omega) (by omega),
        readW64_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [readW64_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-! ## Calling the block function -/

/-- The registers the block function never writes. -/
def kept : List Reg := [.r3, .r4]

theorem block_keeps : ((instrs Impl.ChaCha20.PPC64LE.block).all fun i =>
    kept.all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem block_keeps_reg {r : Reg} (hr : r ∈ kept) :
    ∀ i ∈ instrs Impl.ChaCha20.PPC64LE.block, dstOf i ≠ some r := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp block_keeps i hi) r hr
  simpa using this

theorem block_noFrames : Impl.ChaCha20.PPC64LE.block.noFrames = true := by decide +kernel

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends OInv s₀ j s where
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : OInv s₀ j s) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) s
      fun s' => AInv s₀ j s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  have c3 : s.callEntry.gpr .r3 = st s₀ := (State.callEntry_gpr _ (by decide)).trans h.r3
  have c4 : s.callEntry.gpr .r4 = bp s₀ := (State.callEntry_gpr _ (by decide)).trans h.r4
  have hwr : s.wr = [stR s₀, dR s₀, bR s₀] := by rw [h.wr, hp.wr]
  have hrd : s.rd = [] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockPPC64LE) block_verified.1
    (rd := [stR s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_ block_noFrames
  · simp only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (b256_sub s₀)).symm⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ _ hf hcs hkeep hpost
    have hst : stateAt s₂.mem (st s₀) = stateAt s.mem (st s₀) :=
      stateAt_frame hf (by simpa using hp.st_b.sub_right (b256_sub s₀))
    simp only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, h.cnt] at hpost
    refine ⟨⟨⟨by rw [hkeep .r3 (by decide) (block_keeps_reg (by simp [kept])), h.r3],
      by rw [hkeep .r4 (by decide) (block_keeps_reg (by simp [kept])), h.r4],
      by rw [hcs .r22 (by decide), h.r22],
      by rw [hcs .r23 (by decide), h.r23],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], by rw [hst, h.cnt], fun k hk => ?_,
      h.saved.frame hf (by simpa using savR_b256 s₀)⟩, fun t ht => ?_⟩,
      fun r hr => hcs r (by revert r; decide)⟩
    · rw [hf.bytes (R := dR s₀) (by simpa using hp.d_b.sub_right (b256_sub s₀)) (L_lt s₀).le hk]
      exact h.data k hk
    · rw [← serialize_stateAt s₂.mem (bp s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r4 : s.gpr .r4 = bp s₀
  r22 : s.gpr .r22 = dp s₀ + BitVec.ofNat 64 (P s₀ j + i)
  r7 : s.gpr .r7 = bp s₀ + BitVec.ofNat 64 i
  r5 : s.gpr .r5 = BitVec.ofNat 64 (C s₀ j - i)
  r23 : s.gpr .r23 = BitVec.ofNat 64 (L s₀ - P s₀ j - C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j + i then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : Saved s₀ s.mem
  ks : ∀ t < 64, s.mem (bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

def selProg : Prog isa :=
  .seq (.block [.lsr .d .r9 .r23 6, mov .r5 .r23])
    (.seq (.ite (.zero .d .r9) (.block []) (.block [.li .r5 64]))
      (.block [.sub .r23 .r23 .r5, mov .r7 .r4]))

theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa selProg s (IInv s₀ j 0) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have hr9 : s₂.gpr .r9 = BitVec.ofNat 64 ((L s₀ - P s₀ j) / 64) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.r23, ofNat_shr6 (by omega)]
  have hr5 : s₂.gpr .r5 = BitVec.ofNat 64 (L s₀ - P s₀ j) := by
    rw [u₂.gpr, u₁.other _ (by decide), h.r23]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .r5 = BitVec.ofNat 64 (C s₀ j) ∧
      (∀ r, r ≠ .r5 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂, f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((L s₀ - P s₀ j) / 64 = 0))
      (by rw [eval_zero, hr9, ofNat_beq_zero (by omega)])
      (fun ht => WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩)
      (fun hf => wp_li (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [hr5, show C s₀ j = L s₀ - P s₀ j by omega]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show C s₀ j = 64 by omega]
  · refine wp_sub fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .r5 → r ≠ .r23 → r ≠ .r7 → r ≠ .r9 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ => by rw [u₅.other r h₃, u₄.other r h₂, f₂ r h₁, u₂.other r h₁, u₁.other r h₄]
    have gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, u₂.mem, u₁.mem]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r3],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r4],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), h.r22, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂ _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.r4]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂ _ (by decide), f₁, u₂.other _ (by decide),
        u₁.other _ (by decide), h.r23, sub_ofNat (by omega)],
      by rw [u₅.rd, u₄.rd, f₄, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, u₂.wr, u₁.wr, h.wr],
      by rw [gm, h.cnt], fun k hk => by rw [gm, h.data k hk, Nat.add_zero],
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.lbz .r6 .r22 0, .lbz .r8 .r7 0, .logic .xor .r6 .r6 .r8, .stb .r6 .r22 0,
    .addi .r22 .r22 1, .addi .r7 .r7 1, .subi .r5 .r5 1]

theorem xorLoop_eq : xorLoop = .loop (.block xorBody) (.nonzero .d .r5) := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem xor_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) : WP isa (.block xorBody) s (IInv s₀ j (i + 1)) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  have hk : P s₀ j + i < L s₀ := by omega
  have cd : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    contains_off (by omega) (by omega)
  have cb : (bR s₀).Contains (bp s₀ + BitVec.ofNat 64 i) 1 := contains_off (by omega) (by omega)
  have i₁ : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dR s₀, by simp [h.wr, hp.wr], cd⟩
  unfold xorBody
  refine wp_lbz (a := dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide) (by decide)
    (by rw [h.r22]; exact BitVec.add_zero _) i₁ fun s₁ u₁ => ?_
  refine wp_lbz (a := bp s₀ + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.r7]; exact BitVec.add_zero _)
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_stb (a := dp s₀ + BitVec.ofNat 64 (P s₀ j + i)) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r22]
        exact BitVec.add_zero _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_addi (by decide) (by decide) fun s₅ u₅ => wp_addi (by decide) (by decide) fun s₆ u₆ =>
    wp_subi (by decide) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : (s₃.gpr .r6).setWidth 8 =
      D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, xor_setWidth, h.data _ hk,
      h.ks i (by omega), ks_eq hj hi]
    simp
  have hm : s₇.mem = s.mem.writeW (dp s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  have hfd : Frame [dR s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .r6 → r ≠ .r8 → r ≠ .r22 → r ≠ .r7 → r ≠ .r5 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, g₄.gpr, u₃.other r h₁, u₂.other r h₂,
        u₁.other r h₁]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r3],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4], ?_, ?_, ?_,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r23],
    by rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [stateAt_frame hfd (by simpa using hp.st_d), h.cnt], fun k hk' => ?_,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (savR_sub s₀)).symm), fun t ht => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r22, add_ofNat, Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r7, add_ofNat]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r5, sub_ofNat (by omega), Nat.sub_sub]
  · rw [hm, writeW8_apply]
    by_cases he : k = P s₀ j + i
    · subst he; simp
    · simp only [data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < P s₀ j + (i + 1) by omega]
  · rw [hfd.bytes (R := bR s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  have hpos : 0 < C s₀ j := by simp only [C]; omega
  have hC : C s₀ j ≤ 64 := by simp only [C]; omega
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (isa.eval (.nonzero .d .r5) s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
      (isa.eval (.nonzero .d .r5) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' h' => ?_
    have hz := eval_nonzero_ofNat s' .r5 (by omega) h'.r5
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## The end of a block -/

def nextInstrs : List Instr := [.load .w .r8 .r3 48, .addi .r8 .r8 1, .store .w .r8 .r3 48]

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) : WP isa (.block nextInstrs) s (OInv s₀ (j + 1)) := by
  have hP := P_succ hj
  have c₁ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 48) 4 := contains_off (by omega) (by omega)
  unfold nextInstrs
  refine wp_lwz (by decide) (by decide) (by rw [h.r3]) ⟨stR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩
    fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_stw (by decide) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r3])
    ⟨stR s₀, by simp [u₂.wr, u₁.wr, h.wr, hp.wr], c₁⟩ fun s₃ g₃ => WP.block_nil ?_
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12] := by
    rw [← h.cnt]; simp [stateAt]
  have hm : s₃.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12] + 1) := by
    rw [g₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, inc_setWidth, hv]
  have hfs : Frame [stR s₀] s.mem s₃.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have g : ∀ r, r ≠ .r8 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃.gpr, u₂.other r hr, u₁.other r hr]
  refine ⟨by rw [g _ (by decide), h.r3], by rw [g _ (by decide), h.r4],
    by rw [g _ (by decide), h.r22, hP], by rw [g _ (by decide), h.r23, hP, Nat.sub_sub],
    by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [hm, stateAt_writeW_counter, h.cnt, ctr_succ], fun k hk => ?_,
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)⟩
  rw [hfs.bytes (R := dR s₀) (by simpa using hp.st_d.symm) (L_lt s₀).le hk, h.data k hk, hP]

/-- The body after the call. -/
def rest : Prog isa :=
  .seq (.block [.lsr .d .r9 .r23 6, mov .r5 .r23])
  (.seq (.ite (.zero .d .r9) (.block []) (.block [.li .r5 64]))
  (.seq (.block [.sub .r23 .r23 .r5, mov .r7 .r4])
  (.seq xorLoop (.block nextInstrs))))

theorem body_eq : body = .seq (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) rest := rfl

theorem rest_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : AInv s₀ j s) : WP isa rest s (OInv s₀ (j + 1)) := by
  have hs := sel_ok hj h
  unfold selProg at hs
  rw [WP.seq_iff] at hs
  rw [rest, WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (xorLoop_ok hp hj h₄) fun s₅ h₅ => next_ok hp hj h₅)

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) (hnv : NV s₀ s) : WP isa body s fun s' => OInv s₀ (j + 1) s' ∧ NV s₀ s' := by
  rw [body_eq]
  refine WP.seq (WP.mono (call_ok hp h) fun s₁ ⟨h₁, nv₁⟩ => ?_)
  exact WP.mono (WP.gprs (rs := nvRegs) (rest_ok hp hj h₁) (by decide)) fun s₂ ⟨h₂, nv₂⟩ =>
    ⟨h₂, fun r hr => (nv₂ r hr).trans ((nv₁ r hr).trans (hnv r hr))⟩

/-! ## The epilogue -/

theorem restore_eq : restore =
    [.load .d .r0 .r4 272, .mtlr .r0, .load .d .r22 .r4 256, .load .d .r23 .r4 264] := rfl

/-- What the code guarantees on return, beyond the registers it never writes. -/
def Post (s₀ s' : State) : Prop :=
  s'.gpr .r22 = s₀.gpr .r22 ∧ s'.gpr .r23 = s₀.gpr .r23 ∧ s'.lr = s₀.lr ∧
    Proof.ChaCha20.xorPPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : OInv s₀ j s) : WP isa (.block restore) s (Post s₀) := by
  have i : ∀ d, d + 8 ≤ 320 → InRegions (s.rd ++ s.wr) (bp s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], contains_off hd (by omega)⟩
  obtain ⟨sv1, sv2, sv3⟩ := h.saved
  rw [restore_eq]
  refine wp_ld (by decide) (by decide) (by rw [h.r4]) (i 272 (by omega)) fun s₁ u₁ => ?_
  refine wp_mtlr fun s₂ g₂ l₂ => ?_
  refine wp_ld (by decide) (by decide) (by rw [g₂.gpr, u₁.other _ (by decide), h.r4])
    (by rw [g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact i 256 (by omega)) fun s₃ u₃ => ?_
  refine wp_ld (by decide) (by decide)
    (by rw [u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r4])
    (by rw [u₃.rd, u₃.wr, g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact i 264 (by omega)) fun s₄ u₄ =>
    WP.block_nil ?_
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem]
  refine ⟨by rw [u₄.other _ (by decide), u₃.gpr, g₂.mem, u₁.mem, sv1],
    by rw [u₄.gpr, u₃.mem, g₂.mem, u₁.mem, sv2],
    by rw [u₄.lr, u₃.lr, l₂, u₁.gpr, sv3], ?_⟩
  refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
  have hk' : k < L s₀ := hk
  rw [hm, h.data k hk']
  simp only [show k < P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.PPC64LE.Xor.xor =
    .seq (.block (save ++ [mov .r22 .r4, mov .r23 .r5, mov .r4 .r6]))
    (.seq (.ite (.zero .d .r23) (.block []) (.loop body (.nonzero .d .r23))) (.block restore)) := rfl

theorem main_ok {s₀ : State} (hp : XPre s₀) :
    WP isa Impl.ChaCha20.PPC64LE.Xor.xor s₀ fun s' => Post s₀ s' ∧ NV s₀ s' := by
  have hL := L_lt s₀
  rw [xor_eq]
  refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) (by decide)) fun s₁ ⟨h₁, nv₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s ∧ NV s₀ s) ?_
    fun s₂ ⟨j, hj, h₂, nv₂⟩ => WP.mono (WP.gprs (rs := nvRegs) (epilogue_ok hp hj h₂) (by decide))
      fun s₃ ⟨h₃, nv₃⟩ => ⟨h₃, fun r hr => (nv₃ r hr).trans (nv₂ r hr)⟩)
  have hz : isa.eval (.zero .d .r23) s₁ = some (decide (L s₀ = 0)) := by
    rw [eval_zero, h₁.r23, ofNat_beq_zero (by omega)]
    simp [P]
  refine WP.ite (decide (L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [P, h], h₁, nv₁⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv : Nat → State → Prop := fun n s =>
      ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s ∧ NV s₀ s
    have hstep : ∀ n s, Inv n s → WP isa body s (fun s' =>
        (isa.eval (.nonzero .d .r23) s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ OInv s₀ j s' ∧ NV s₀ s') ∨
        (isa.eval (.nonzero .d .r23) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, hI, hnv⟩
      refine WP.mono (body_ok hp hj hI hnv) fun s' ⟨h', nv'⟩ => ?_
      have hz' := eval_nonzero_ofNat s' .r23 (by omega) h'.r23
      have hP := P_succ hj
      have hC : 0 < C s₀ j := by simp only [C]; omega
      have hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega, h', nv'⟩
      · exact .inr ⟨by rw [hz']; simp [hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega,
          h', nv'⟩
    exact WP.loop (M := isa) Inv hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega, h₁, nv₁⟩

/-- The callee-saved registers that no instruction writes, including those of
the block function. -/
def untouched : List Reg := [.r2, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs Impl.ChaCha20.PPC64LE.Xor.xor,
    dstOf i ≠ some r := by
  have : ((instrs Impl.ChaCha20.PPC64LE.Xor.xor).all fun i =>
      untouched.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem correct {s₀ : State} (hp : XPre s₀) :
    ∃ t s', Exec isa Impl.ChaCha20.PPC64LE.Xor.xor s₀ t s' ∧ abiPreserved s₀ s' ∧
      Proof.ChaCha20.xorPPC64LE.post s₀ s' := by
  obtain ⟨t, s', he, ⟨h22, h23, hlr, hpost⟩, hnv⟩ := main_ok hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hlr⟩, hpost⟩
  have hl : ∀ r ∈ untouched, r ∉ linkRegs := by decide
  have key : ∀ r ∈ preserved, r = .r22 ∨ r = .r23 ∨ r ∈ nvRegs ∨ r ∈ untouched := by decide
  rcases key r hr with rfl | rfl | h | h
  · exact h22
  · exact h23
  · exact hnv r h
  · exact Exec.gpr (untouched_ok r h) he (.inr (hl r h))

/-! ## Constant time -/

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.ChaCha20.xorPPC64LE.pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.PPC64LE.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorPPC64LE.post s s' :=
  correct (XPre.of s hs)

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorPPC64LE.pre Proof.ChaCha20.xorPPC64LE.pub
    Impl.ChaCha20.PPC64LE.Xor.xor :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)

theorem xor_verified :
    Verified PPC64LE.target Impl.ChaCha20.PPC64LE.Xor.xor (Spec.ChaCha20.xorContract PPC64LE.abi) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, PPC64LE.abi, PPC64LE.argRegs,
      Proof.ChaCha20.xorPPC64LE]
      [sat] using sat)

end VG.Proof.ChaCha20.PPC64LE.Xor
