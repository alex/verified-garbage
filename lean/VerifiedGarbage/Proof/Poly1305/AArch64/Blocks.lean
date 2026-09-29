import VerifiedGarbage.Proof.Poly1305.AArch64.Setup
import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Poly1305 on AArch64: `blocks`

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305

open Spec.Poly1305

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let key : Region := ⟨s.gpr .x1, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .x0) (bytesAt s.mem (s.gpr .x1) 32) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let blocks : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .x0) key msg →
    Repr s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x1) (16 * (s.gpr .x2).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, …)`:
only `count mod 16`, the number of bytes buffered, matters. The state must be
writable, and it may be permitted to write other regions (which it does
not). -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    s.rd = [data] ∧ state ∈ s.wr ∧ state.Disjoint data
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
`vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], …)`:
only `count mod 16`, the number of bytes buffered, matters. The state and
`out` must be writable, and it may be permitted to write other regions
(which it does not). -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let out : Region := ⟨s.gpr .x2, 16⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .x2) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem mod_step {h X M R : Nat} (hv : h % P = X % P) :
    ((h + M) * R) % P = (R * (X + M)) % P % P := by
  rw [Nat.mod_mod, Nat.mul_comm R, Nat.mul_mod, Nat.add_mod, hv, ← Nat.add_mod, ← Nat.mul_mod]

/-! ## Common to `blocks` and `finalize` -/

section
variable (s₀ : State)
/-- The state, on entry. -/
abbrev st : Addr := s₀.gpr .x0
/-- The clamped `r`. -/
abbrev Rn : Nat := Rk s₀.mem (st s₀)
/-- The accumulator on entry. -/
abbrev A0 : Nat := leNum (bytesAt s₀.mem (st s₀) 24)
end

/-- The memory `setup` leaves. -/
structure Mem₁ (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [cR (st s₀)] s₀.mem m₁
  coefs : Coefs m₁ (st s₀) (Rn s₀)

theorem cR_sub_wR (st : Addr) : Region.Sub (cR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off] at *
  bv_omega

theorem cR_sub_sR (st : Addr) : Region.Sub (cR st) (sR st) := sub_sR st (by omega)

/-- The accumulator on entry is less than `p` if the state represents a message. -/
theorem A0_lt {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) : A0 s₀ < P := by
  have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
  rw [← h.2.2] at this
  exact this

theorem off_24 (p : Addr) : off p 24 = p + 24 := rfl

/-- The key of a state that represents a message, and its clamped `r`. -/
theorem repr_key {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    bytesAt s₀.mem (off (st s₀) 24) 32 = key := h.2.1

theorem repr_acc {s₀ : State} {key msg : List Byte} (h : Repr s₀.mem (st s₀) key msg) :
    accumulate (Rn s₀) msg = A0 s₀ := by
  rw [A0, h.2.2, ← repr_key h, clamp_key]

/-- The words of `h` stored. -/
def storeHm (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) : Mem :=
  ((m.writeW (off st 0) w0).writeW (off st 8) w1).writeW (off st 16) w2

set_option simprocs false in
theorem storeH_ok (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block storeH) s fun s' =>
      s'.mem = storeHm s.mem (s.gpr .x0) (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .x0) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega)⟩
  have o0 := o 0 (by omega); have o8 := o 8 (by omega); have o16 := o 16 (by omega)
  simp only [off] at o0 o8 o16
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeH, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    exec_str_x (show 16 % 8 = 0 ∧ 16 < 32768 by decide), o8, o16, Option.some.injEq, exists_eq_left']
  trivial

theorem storeHm_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') (w0 w1 w2 : BitVec 64) :
    Frame [hR st, wR st] m (storeHm m' st w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
  exact ((hf.writeW List.mem_cons_self _ (c 0 (by omega))).writeW List.mem_cons_self _
    (c 8 (by omega))).writeW List.mem_cons_self _ (c 16 (by omega))

set_option simprocs false in
theorem storeHm_acc (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) :
    leNum (bytesAt (storeHm m st w0 w1 w2) st 24) = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat := by
  rw [leNum_acc]
  simp (config := {decide := true}) only [w64, storeHm, readW_writeW_off,
    Mem.readW_writeW_self64]

/-- No instruction of `c` writes a callee-saved register. -/
def Untouched (c : Prog isa) : Prop := ∀ r ∈ preserved, ∀ i ∈ instrs c, dstOf i ≠ some r

theorem Untouched.of_all {c : Prog isa}
    (h : ((instrs c).all fun i => preserved.all fun r => dstOf i != some r) = true) : Untouched c := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-! ## `blocks` -/

section
variable (s₀ : State)
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev blR : Region := ⟨bp s₀, 16 * nb s₀⟩
/-- The first `i` blocks. -/
abbrev blks (i : Nat) : List Byte := bytesAt s₀.mem (bp s₀) (16 * i)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (16 * i)
end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem BPre.of (s₀ : State) (h : Proof.Poly1305.blocksAArch64.pre s₀) : BPre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- What holds between blocks, after `i` of them, with the memory `m₁` left
by `setup`. -/
structure Common (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  mask : s.gpr .x17 = M26
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ i) % P ∧ Bounds s

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (m₁ : Mem) (i : Nat) (s : State) : Prop extends Common s₀ m₁ i s where
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  have := (bp s₀).isLt
  by_contra h
  refine hp.st_bl (st s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem blk_contains {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := hp.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 d = bp s₀ + BitVec.ofNat 64 (16 * i + d) by
    simp only [blkAddr]; bv_omega]
  exact contains_off (by omega) (by omega)

/-- Block words, in memory the code has written only in the coefficients. -/
theorem blk_word {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m) {i d : Nat} (hi : i < nb s₀)
    (hd : d + 8 ≤ 16) :
    m.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 = s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 d) 64 :=
  hf.readW (hp.blk_contains hi hd) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_bl.symm.sub_right (cR_sub_sR _)) (by decide)

theorem coefIn {s : State} (hx0 : s.gpr .x0 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CoefIn s := fun off h₁ h₂ => by
  rw [hrd, hwr, hx0, hp.wr]
  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), contains_off (by omega) (by omega)⟩

end BPre

set_option simprocs false in
theorem advance_ok (s : State) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 16 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1 ∧
      Keeps [.x1, .x2] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, runBlock_cons, runStep_some, runBlock_nil,
    exec_addImm_x (show 16 < 4096 by decide), exec_subImm_x (show 1 < 4096 by decide), State.read,
    State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

/-- The value of block `i`, with the `0x01` byte appended: its two words and `2¹²⁸`. -/
theorem block_value {s₀ : State} (hp : BPre s₀) {m : Mem} (hf : Frame [cR (st s₀)] s₀.mem m)
    {i : Nat} (hi : i < nb s₀) :
    w64 m (blkAddr s₀ i) 0 + 2 ^ 64 * w64 m (blkAddr s₀ i) 8 + 2 ^ 128 * true.toNat =
      leNum (bytesAt s₀.mem (blkAddr s₀ i) 16 ++ [0x01]) := by
  simp only [w64]
  rw [hp.blk_word hf hi (by omega), hp.blk_word hf hi (by omega), Poly1305.leNum_append,
    Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

theorem blks_succ (s₀ : State) (i : Nat) :
    blks s₀ (i + 1) = blks s₀ i ++ bytesAt s₀.mem (blkAddr s₀ i) 16 := by
  simp only [blks, blkAddr]
  rw [show 16 * (i + 1) = 16 * i + 16 by omega, Poly1305.bytesAt_add]

theorem bounds_eq {s s' : State} (h : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], s'.gpr r = s.gpr r) :
    hv s' = hv s ∧ (Bounds s → Bounds s') := by
  have e : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], v s' r = v s r := fun r hr => by simp only [v, h r hr]
  refine ⟨by simp only [hv, e .x4 (by simp), e .x5 (by simp), e .x6 (by simp), e .x7 (by simp),
    e .x8 (by simp)], fun hb => ?_⟩
  simp only [Bounds, e .x4 (by simp), e .x5 (by simp), e .x6 (by simp), e .x7 (by simp),
    e .x8 (by simp)]
  exact hb

theorem body_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {i : Nat}
    (hi : i < nb s₀) {s : State} (hL : LInv s₀ m₁ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ m₁ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ m₁ (i + 1) s') := by
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [hL.rd, hL.wr, hL.x1, hp.rd]
    exact ⟨blR s₀, List.mem_append_left _ (List.mem_singleton_self _), hp.blk_contains hi hd⟩
  have hab := absorb_ok s true (Rk_lt _ _) hL.mask (by rw [hL.mem, hL.x0]; exact hm.coefs)
    (hp.coefIn hL.x0 hL.rd hL.wr) (hin 0 (by omega)) (hin (0 + 8) (by omega))
  rw [body]
  refine WP.block_append (WP.mono hab fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hc : Common s₀ m₁ (i + 1) s₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun hA => ?_⟩
    · rw [k.gpr' (r := .x0), hL.x0]
    · rw [k.gpr' (r := .x17), hL.mask]
    · rw [k.2.2.1, hL.rd]
    · rw [k.2.2.2, hL.wr]
    · rw [k.2.1, hL.mem]
    · obtain ⟨hv₀, hb⟩ := hL.acc hA
      obtain ⟨hv', hb'⟩ := ha hb
      obtain ⟨e₂, b₂⟩ := bounds_eq (s := s₁) (s' := s₂) fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      refine ⟨?_, b₂ hb'⟩
      have h16 : (blks s₀ i).length % 16 = 0 := by
        simp only [blks, Poly1305.length_bytesAt]; omega
      have hb1 : 0 < (bytesAt s₀.mem (blkAddr s₀ i) 16).length := by
        rw [Poly1305.length_bytesAt]; omega
      have hb2 : (bytesAt s₀.mem (blkAddr s₀ i) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
      rw [e₂, hv', hL.x1, hL.mem, block_value hp hm.frame hi, mod_step hv₀, blks_succ,
        Poly1305.absorbAll_append h16, Poly1305.absorbAll_block hb1 hb2]
  have hx2 : s₂.gpr .x2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [a₂, k₁.gpr' (r := .x2), hL.x2]
    have := hp.nb_lt
    bv_omega
  have hev : eval (.nonzero .x .x2) s₂ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hc⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hc with x1 := ?_, x2 := hx2 }⟩
    rw [a₁, k₁.gpr' (r := .x1), hL.x1]
    simp only [blkAddr]
    bv_omega

/-! ## Epilogue -/

theorem words_val (V : Nat) :
    V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64 % 2 ^ 64) + 2 ^ 128 * (V / 2 ^ 128) = V := by omega

theorem Mem₁.frame_wR {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) :
    Frame [hR (st s₀), wR (st s₀)] s₀.mem m₁ :=
  hm.frame.sub fun r hr => ⟨wR (st s₀), by simp, by
    simp only [List.mem_singleton] at hr; subst hr; exact cR_sub_wR _⟩

theorem epilogue_ok {s₀ : State} (hp : BPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s : State}
    (hc : Common s₀ m₁ (nb s₀) s) :
    WP isa (.block (reduce ++ pack ++ storeH)) s fun s' => Proof.Poly1305.blocksAArch64.post s₀ s' := by
  refine WP.block_append (WP.block_append (WP.mono (reduce_ok s hc.mask) fun s₁ ⟨hr, k₁⟩ =>
    WP.mono (pack_ok s₁) fun s₂ ⟨hp₂, k₂⟩ => ?_))
  have x0₂ : s₂.gpr .x0 = st s₀ := by rw [k₂.gpr', k₁.gpr', hc.x0]
  refine WP.mono (storeH_ok s₂ (by
    rw [k₂.2.2.2, k₁.2.2.2, hc.wr, hp.wr, x0₂]; exact List.mem_singleton_self _))
    fun s₃ ⟨m₃, _, _, _⟩ => ?_
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hc.acc hA
  obtain ⟨hN, n0, n1, n2, n3, -⟩ := hr hb
  obtain ⟨w0, w1, w2⟩ := hp₂ n0 n1 n2 n3
  have mem₂ : s₂.mem = m₁ := by rw [k₂.2.1, k₁.2.1, hc.mem]
  rw [x0₂, mem₂] at m₃
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₃.mem := by
    rw [m₃]; exact storeHm_frame hm.frame_wR _ _ _
  have hlen := hrep.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, Poly1305.length_bytesAt]; omega
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₃, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    have hV : val5 (v s₁ .x4) (v s₁ .x5) (v s₁ .x6) (v s₁ .x7) (v s₁ .x8) =
        Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (nb s₀)) := by
      rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    change v s₂ .x14 + 2 ^ 64 * v s₂ .x15 + 2 ^ 128 * v s₂ .x16 = _
    rw [w0, w1, w2, words_val, hV]

/-! ## The whole function -/

theorem blocks_correct {s₀ : State} (hp : BPre s₀) :
    WP isa blocks s₀ (Proof.Poly1305.blocksAArch64.post s₀) := by
  refine WP.seq (WP.mono (setup_ok s₀ (by rw [hp.wr]; exact List.mem_singleton_self _))
    fun s₁ h₁ => ?_)
  have hm : Mem₁ s₀ s₁.mem := ⟨h₁.frame, h₁.coefs⟩
  have hc₀ : Common s₀ s₁.mem 0 s₁ := ⟨h₁.gpr .x0 (by decide), h₁.mask, h₁.rd, h₁.wr, rfl,
    fun hA => by
      obtain ⟨e, b⟩ := h₁.acc hA
      refine ⟨?_, b⟩
      rw [e, show blks s₀ 0 = [] by simp [blks, bytesAt], Poly1305.absorbAll_nil]⟩
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := h₁.gpr .x2 (by decide)
  refine WP.seq (WP.mono (Q := Common s₀ s₁.mem (nb s₀)) ?_ fun s₂ hc₂ => epilogue_ok hp hm hc₂)
  refine WP.ite (s₁.read .x .x2 == 0) rfl (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_iff_eq] at h
      simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ s₁.mem i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ s₁.mem (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hm hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ s₁.mem 0 s₁ :=
      { hc₀ with
        x1 := by rw [h₁.gpr .x1 (by decide)]; simp [blkAddr]
        x2 := by rw [x2₁]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def blocksSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem blocks_untouched : Untouched Impl.Poly1305.AArch64.blocks :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem blocks_ok (s : State) (hs : Proof.Poly1305.blocksAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.blocks s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.blocksAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := blocks_correct (BPre.of s hs)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (blocks_untouched r hr) he, Exec.sp he⟩, h⟩

theorem blocks_ct : ConstantTime isa Proof.Poly1305.blocksAArch64.pre
    Proof.Poly1305.blocksAArch64.pub Impl.Poly1305.AArch64.blocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> assumption

theorem blocks_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.blocks (Spec.Poly1305.blocksContract AArch64.abi)
      :=
  Verified.of_correct blocks_ok blocks_ct (by
    sig_implies [Spec.Poly1305.blocksContract, Spec.Poly1305.blocksSig,
      Proof.Poly1305.blocksAArch64, AArch64.abi, AArch64.argRegs] [Proof.Poly1305.AArch64.blocksSat]
      using Proof.Poly1305.AArch64.blocksSat)

end VG.Proof.Poly1305.AArch64
