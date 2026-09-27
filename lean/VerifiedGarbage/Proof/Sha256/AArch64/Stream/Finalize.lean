import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common

/-!
# Streaming SHA-256 on AArch64: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Sha256.X86_64.Stream.Finalize`).
-/

namespace VG.Proof.Sha256.AArch64.Stream.Finalize

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (contains_offset toNat_ofNat_lt sub_offset)
open VG.Proof.Sha256.AArch64.Stream
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev out : Addr := s₀.gpr .x2
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 32⟩
abbrev scR : Region := ⟨scr s₀, 160⟩

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha256.Repr s₀.mem (st s₀) m ∧ s₀.gpr .x1 = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (st s₀))
    (parseBlock fun t => (bytesAt mem (st s₀ + 32) n ++ List.replicate (64 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (st s₀))
    (parseBlock fun t => (bytesAt mem (st s₀ + 32) n ++ List.replicate (56 - n) 0 ++ lenBytes m).getD t 0)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, outR s₀, scR s₀]
  st_out : (stR s₀).Disjoint (outR s₀)
  st_scr : (stR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Spec.Sha256.finalizeAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem R₀.length {s₀ : State} {m : List Byte} (h : R₀ s₀ m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem st_add (s₀ : State) (n : Nat) :
    st s₀ + 32 + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (32 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = out s₀
  x22 : s.gpr .x22 = s₀.gpr .x1
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  x23 : s.gpr .x23 = BitVec.ofNat 64 n
  x24 : s.gpr .x24 = BitVec.ofNat 64 k
  hash : ∀ m, R₀ s₀ m → Spec.Sha256.hash m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ m, R₀ s₀ m → Spec.Sha256.hash m = (stateAt s.mem (st s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.Sha256.AArch64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) ∧
      Frame [stR s₀, scR s₀] s₀.mem (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) := by
  have hf : Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [st_add]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hp')

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x24], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  x9 : s.gpr .x9 = 0
  x23 : s.gpr .x23 = BitVec.ofNat 64 (n + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (st s₀ + 32 + BitVec.ofNat 64 n) (List.replicate j 0)

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.add .x .x12 .x19 .x23, .strb .x9 .x12 32, .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]

theorem zero_step {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block zeroBody) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (lim - n - (j + 1)) := by
  have hx19 : s.gpr .x19 = st s₀ := by rw [h.keep _ (by simp), hC.x19]
  have hout : InRegions s.wr (st s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show st s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = st s₀ + BitVec.ofNat 64 (32 + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  unfold zeroBody
  refine wp_add fun s₁ u₁ => wp_strb (a := st s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega)
    ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19, h.x23, BitVec.ofNat_add, show BitVec.ofNat 64 32 = (32 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addImm (by omega) fun s₃ u₃ => wp_subImm (by omega) fun s₄ u₄ => WP.block_nil ⟨⟨by omega,
    fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .x11 ∧ r ≠ .x23 ∧ r ≠ .x12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x9]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x11,
      sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.x9, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x11,
      sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s) :
    WP isa (.ite (.zero .x .x11) (.block []) (.loop (.block zeroBody) (.nonzero .x .x11))) s
      (Zero s₀ sI n lim (lim - n)) := by
  have hz : eval (.zero .x .x11) s = some (decide (lim - n = 0)) := by
    rw [eval_zero, h.x11, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', h11⟩ => ?_
    have hz' : isa.eval (.nonzero .x .x11) s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x11) s' = _
      rw [eval_nonzero, h11, bne, ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The inlined compression of the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s)
    (hx1 : s.gpr .x1 = st s₀ + 32) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (st s₀) = compress (stateAt s.mem (st s₀)) (blockAt s.mem (st s₀ + 32)) → Q s') :
    WP isa compressAt s Q := by
  have e32 : Region.Sub ⟨st s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scr s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨st s₀ + 32, 64⟩ (stR s₀) := sub_offset (off := 32) (by omega) (by omega)
  refine compressAt_ok hC.x19 hC.x20 hx1 ((hp.st_scr.sub_left e32).sub_right e112) ?_
    ((hp.st_scr.sub_left eb).sub_right e112) ?_ ?_ fun s' hrd hwr hcs hsp hf hstate =>
      hQ s' ?_ hcs hstate
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 32, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · have cs : ∀ r, r ∈ preserved → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.x19,
      by rw [cs _ (by decide)]; exact hC.x20, by rw [cs _ (by decide)]; exact hC.x21,
      by rw [cs _ (by decide)]; exact hC.x22, hsp.trans hC.sp, hC.frame.trans (hf.sub ?_),
      fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
    · rw [← hC.saved p hp']
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · simp only [Impl.Sha256.AArch64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

theorem len_bits {m : List Byte} {x : BitVec 64} (hx : x = BitVec.ofNat 64 m.length) :
    BitVec.ofNat 64 (8 * x.toNat) = BitVec.ofNat 64 (8 * m.length) := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval (.zero .x .x24) s = some false ∧ Done s₀ s) ∨
    (eval (.zero .x .x24) s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem body_eq : finalizeBody =
    .seq (.block [.movz .x .x11 64 0])
    (.seq (.ite (.zero .x .x24) (.block [.movz .x .x11 56 0]) (.block []))
    (.seq (.block [.movz .x .x9 0 0, .sub .x .x11 .x11 .x23])
    (.seq (.ite (.zero .x .x11) (.block []) (.loop (.block zeroBody) (.nonzero .x .x11)))
    (.seq (.ite (.zero .x .x24)
        (.block [.add .x .x9 .x22 .x22, .add .x .x9 .x9 .x9, .add .x .x9 .x9 .x9, .rev .x9 .x9,
          .str .x .x9 .x19 88])
        (.block []))
    (.seq (.block [.addImm .x .x1 .x19 32])
    (.seq compressAt (.block [.movz .x .x23 0 0, .subImm .x .x24 .x24 1]))))))) := rfl

set_option maxHeartbeats 2000000 in
theorem body_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  rw [body_eq]
  -- `x11 := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_movz fun s₁ u₁ => WP.block_nil ?_)
  have hz₁ : eval (.zero .x .x24) s₁ = some (decide (k = 0)) := by
    rw [eval_zero, u₁.other _ (by decide), h.x24, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .x11 = BitVec.ofNat 64 (56 + 8 * k) ∧
      (∀ r, r ≠ .x11 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h11₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₁ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_movz fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; decide, fun r hr => ?_,
        by rw [u₃.mem, u₁.mem], by rw [u₃.rd, u₁.rd], by rw [u₃.wr, u₁.wr], by rw [u₃.sp, u₁.sp]⟩
      rw [u₃.other r hr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [u₁.gpr, show k = 1 by omega]; decide, fun r hr => ?_,
        u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
      rw [u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (wp_movz fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hZ : Zero s₀ s n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .x11 ∧ r ≠ .x9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.x23, Nat.add_zero]
    · rw [u₅.gpr, u₄.other _ (by decide), h11₃, u₄.other _ (by decide), g₃ _ (by decide), h.x23,
        sub_ofNat (by omega), Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (56 + 8 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.x19],
      by rw [hZ₆.keep _ (by simp), hC.x20], by rw [hZ₆.keep _ (by simp), hC.x21],
      by rw [hZ₆.keep _ (by simp), hC.x22], hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : stateAt s₆.mem (st s₀) = stateAt s.mem (st s₀) := by
    rw [hZ₆.mem]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (st s₀ + 32) (56 + 8 * k) =
      bytesAt s.mem (st s₀ + 32) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h24₆ : s₆.gpr .x24 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.x24]
  -- In the last block, the length.
  have hz₆ : eval (.zero .x .x24) s₆ = some (decide (k = 0)) := by
    rw [eval_zero, h24₆, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .x24 = BitVec.ofNat 64 k ∧
      stateAt s₈.mem (st s₀) = stateAt s.mem (st s₀) ∧
      ∀ m, R₀ s₀ m → bytesAt s₈.mem (st s₀ + 32) 64 = bytesAt s.mem (st s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)) ?_
    fun s₈ ⟨hC₈, h24₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₆ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hout : InRegions s₆.wr (st s₀ + BitVec.ofNat 64 88) 8 :=
        ⟨stR s₀, by simp [hC₆.wr, hp.wr], contains_offset (by omega) (by omega)⟩
      refine wp_add fun s₇ u₇ => wp_add fun s₈ u₈ => wp_add fun s₉ u₉ => wp_rev fun s₁₀ u₁₀ =>
        wp_str (a := st s₀ + BitVec.ofNat 64 88) (by decide) ?_ ?_ fun s₁₁ g₁₁ => WP.block_nil ?_
      · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
          u₇.other _ (by decide), hC₆.x19]
      · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr]; exact hout
      have keep : ∀ r, r ≠ .x9 → s₁₁.gpr r = s₆.gpr r := fun r h => by
        rw [g₁₁.gpr, u₁₀.other r h, u₉.other r h, u₈.other r h, u₇.other r h]
      have hv : s₁₀.gpr .x9 = X86_64.bswap64 (BitVec.ofNat 64 (8 * (s₀.gpr .x1).toNat)) := by
        rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, hC₆.x22, times8]; rfl
      have hm₁₀ : s₁₀.mem = s₆.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
      let L := (List.range 8).map fun j =>
        (X86_64.bswap64 (BitVec.ofNat 64 (8 * (s₀.gpr .x1).toNat))).extractLsb' (8 * j) 8
      have hw : s₁₁.mem = writeBytes s₆.mem (st s₀ + 32 + BitVec.ofNat 64 56) L := by
        rw [g₁₁.mem, hm₁₀, hv, show st s₀ + 32 + BitVec.ofNat 64 56 = st s₀ + BitVec.ofNat 64 88 by
          rw [BitVec.add_assoc]; rfl, Mem.writeW, write_eq_writeBytes]
        rfl
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := 56) (xs := L) (by simp [L])
      refine ⟨⟨g₁₁.rd.trans (by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd]; exact hC₆.rd),
        g₁₁.wr.trans (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr]; exact hC₆.wr),
        by rw [keep _ (by decide), hC₆.x19], by rw [keep _ (by decide), hC₆.x20],
        by rw [keep _ (by decide), hC₆.x21], by rw [keep _ (by decide), hC₆.x22],
        by rw [g₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp]; exact hC₆.sp,
        by rw [hw]; exact hfr, by rw [hw]; exact hsv⟩,
        by rw [keep _ (by decide), h24₆], ?_, fun m hm => ?_⟩
      · rw [hw, ← hst₆]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [L])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₆.mem (st s₀ + 32) 56 L (by simp [L])
        simp only [L, List.length_map, List.length_range] at e
        rw [hw, e, X86_64.Stream.bswap64_bytes, len_bits hm.2, hby₆]
        simp [lenBytes, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₆, h24₆, hst₆, fun m _ => ?_⟩
      rw [hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_addImm (by decide) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common s₀ s₉ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .x1 := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
      rw [u₉.other r this]) u₉.mem u₉.rd u₉.wr u₉.sp
  have hx1 : s₉.gpr .x1 = st s₀ + 32 := by rw [u₉.gpr, hC₈.x19]; rfl
  refine WP.seq (compress_buf hp hC₉ hx1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have h24₁₁ : s₁₁.gpr .x24 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide), u₉.other _ (by decide), h24₈]
  have hblk : ∀ m, R₀ s₀ m → blockAt s₉.mem (st s₀ + 32) = parseBlock fun t =>
      (bytesAt s.mem (st s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0 := by
    intro m hm
    apply parseBlock_congr
    intro t ht
    rw [u₉.mem]
    exact Stream.bytesAt_getD (hby₈ m hm) ht
  -- Next block, if any.
  refine wp_movz fun s₁₂ u₁₂ => wp_subImm (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have hC₁₃ : Common s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .x24 ∧ r ≠ .x23 := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr]) (by rw [u₁₃.sp, u₁₂.sp])
  have hz : eval (.zero .x .x24) s₁₃ = some (decide (k = 1)) := by
    rw [eval_zero, u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁, sub_beq (by omega) (by omega)]
  have hst : ∀ m, R₀ s₀ m → stateAt s₁₃.mem (st s₀) = compress (stateAt s.mem (st s₀)) (parseBlock fun t =>
      (bytesAt s.mem (st s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro m hm
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk m hm, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun m hm => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁]; rfl
    · rw [h.hash m hm]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst m hm]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [hz]; simp, hC₁₃, fun m hm => ?_⟩
    rw [h.hash m hm, hst m hm]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x22 .x1,
    .movz .x .x9 63 0, .logic .and .x .x23 .x22 .x9,
    .movz .x .x9 0x80 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 32, .addImm .x .x23 .x23 1,
    .addImm .x .x24 .x23 7, .lsr .x .x24 .x24 6]

theorem finalize_eq : finalize = .seq (.block (save .x3 ++ prologue))
    (.seq (.loop finalizeBody (.zero .x .x24))
      (.block ((List.range 8).flatMap (fun k =>
        [.ldr .w .x9 .x19 (4 * k), .rev32 .x9 .x9, .str .w .x9 .x21 (4 * k)]) ++ restore))) := rfl

set_option maxHeartbeats 2000000 in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .x3 ++ prologue)) s₀ fun s => ∃ k, LInv s₀ k (cnt s₀ % 64 + 1) s := by
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_movz fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  have hC₇ : Common s₀ s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
      exact (saveMem_frame _ _ _).mono (by simp)
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
      intro p hp'
      exact saveMem_saved _ _ _ p hp'
  have hm₇ : s₇.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hr23 : s₇.gpr .x23 = BitVec.ofNat 64 (cnt s₀ % 64) := by
    rw [u₇.gpr, u₆.other .x22 (by decide), u₆.gpr, u₅.gpr, u₄.other .x1 (by decide),
      u₃.other .x1 (by decide), u₂.other .x1 (by decide), g₁]
    exact and63 _
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (st s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) 1 := by
    refine ⟨stR s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [st_add]; exact contains_offset (by omega) (by omega)
  refine wp_movz fun s₈ u₈ => wp_add fun s₉ u₉ =>
    wp_strb (a := st s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.x19, hr23,
      show BitVec.ofNat 64 32 = (32 : BitVec 64) from rfl]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hp (n := cnt s₀ % 64) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₇.mem (st s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_addImm (by decide) fun s₁₁ u₁₁ => wp_addImm (by decide) fun s₁₂ u₁₂ =>
    wp_lsr (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .x23 → r ≠ .x24 → r ≠ .x9 → r ≠ .x12 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x19],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x20],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x21],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x22],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr23' : s₁₃.gpr .x23 = BitVec.ofNat 64 (cnt s₀ % 64 + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr23, ← BitVec.ofNat_add]
  have hr24 : s₁₃.gpr .x24 = BitVec.ofNat 64 ((cnt s₀ % 64 + 8) / 64) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr23,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ofNat_shr6 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ m, R₀ s₀ m → bytesAt s₁₃.mem (st s₀ + 32) (cnt s₀ % 64 + 1) = rest m ++ [0x80] := by
    intro m hm
    have e := bytesAt_writeBytes s₇.mem (st s₀ + 32) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    congr 1
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := frame_bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀) (by simpa using hp.st_scr)
      (by simp) (i := 32 + i) (by show 32 + i < 96; omega)
    rwa [← st_add] at this
  have hstate : stateAt s₁₃.mem (st s₀) = stateAt s₀.mem (st s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₇]
    exact frame_bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀) (by simpa using hp.st_scr) (by simp)
      (by show i < 96; omega)
  by_cases hb : 57 ≤ cnt s₀ % 64 + 1
  · have hk : (cnt s₀ % 64 + 8) / 64 = 1 := by omega
    refine ⟨1, hC₁₃, le_rfl, by omega, hr23', by rw [hr24, hk], fun m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, hbytes m hm, hstate, hm.1.1,
      ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 63 - cnt s₀ % 64 by omega]
  · have hk : (cnt s₀ % 64 + 8) / 64 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr23', by rw [hr24, hk], fun m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes m hm, hstate, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 55 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

/-- Word `k` of the digest. -/
def outW (k : Nat) : List Instr := [.ldr .w .x9 .x19 (4 * k), .rev32 .x9 .x9, .str .w .x9 .x21 (4 * k)]

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ [Reg.x19, .x20, .x21], s.gpr r = sD.gpr r
  sp : s.sp = sD.sp
  mem : s.mem = writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.take k).flatMap wordBytes)

theorem flat_length (H : HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap wordBytes).length = 4 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (wordBytes w).length = 4 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate, List.length_take]
  simp; omega

theorem out_frame (s₀ : State) (m : Mem) (xs : List Byte) (hx : xs.length ≤ 32) :
    Frame [outR s₀] m (writeBytes m (out s₀) xs) :=
  writeBytes_frame _ _ _ (by
    rw [show out s₀ = out s₀ + BitVec.ofNat 64 0 by simp]
    exact contains_offset (by omega) (by omega))

theorem writeW_rev32 (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev32 w) = writeBytes m a (wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← X86_64.Stream.bswap32_bytes']; rfl

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by ext i hi; simp

set_option maxHeartbeats 1000000 in
theorem out_step {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {k : Nat} (hk : k < 8)
    {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hx19 : s.gpr .x19 = st s₀ := by rw [h.keep _ (by simp), hC.x19]
  have hx21 : s.gpr .x21 = out s₀ := by rw [h.keep _ (by simp), hC.x21]
  have hP := flat_length (stateAt sD.mem (st s₀)) k hk.le
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_ldr32 (a := st s₀ + BitVec.ofNat 64 (4 * k)) (by omega) (by rw [hx19])
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_rev32 fun s₂ u₂ => wp_str32 (a := out s₀ + BitVec.ofNat 64 (4 * k)) (by omega)
    (by rw [u₂.other .x21 (by decide), u₁.other .x21 (by decide), hx21])
    (by rw [u₂.wr, u₁.wr]; exact ⟨outR s₀, by simp [h.wr, hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₃ g₃ => hnext s₃ ⟨by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
      fun r hr => ?_, by rw [g₃.sp, u₂.sp, u₁.sp, h.sp], ?_⟩
  · have : r ≠ .x9 := by simp at hr; rcases hr with h | h | h <;> subst h <;> decide
    rw [g₃.gpr, u₂.other r this, u₁.other r this, h.keep r hr]
  · have hread : s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = (stateAt sD.mem (st s₀))[k] := by
      rw [h.mem, (out_frame s₀ sD.mem _ (by omega)).readW
        (r := ⟨st s₀ + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hp.st_out.sub_left (sub_offset (by omega) (by omega))
    rw [g₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, sw32, sw32, hread, h.mem, writeW_rev32, ← hP]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ Spec.Sha256.finalizeAArch64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : Out s₀ sD 8 s) : WP isa (.block restore) s (Post s₀) := by
  have hC := hD.1
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes)
    (by rw [flat_length _ _ le_rfl])
  refine restore_ok (scr := scr s₀) (by rw [h.keep _ (by simp), hC.x20])
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, h.sp, hC.sp], ?_⟩
  · rw [h.mem, ← hC.saved p hp']
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (saved_sub hp')
  · intro m hr hc
    have e := bytesAt_writeBytes sD.mem (out s₀) 0 (((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes)
      (by rw [flat_length _ _ le_rfl]; omega)
    have e' : bytesAt (writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes))
        (out s₀) 32 = ((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes := by
      rw [flat_length _ _ le_rfl] at e; simpa [bytesAt] using e
    rw [← h.mem, ← hmem] at e'
    rw [e', hD.2 m ⟨hr, hc⟩, List.take_of_length_le (by simp)]

theorem out_all {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) :
    ∀ j ≤ 8, ∀ s, Out s₀ sD (8 - j) s →
      WP isa (.block (((List.range 8).drop (8 - j)).flatMap outW ++ restore)) s (Post s₀) := by
  intro j
  induction j with
  | zero =>
    intro _ s h
    rw [show (List.range 8).drop (8 - 0) = [] from rfl, List.flatMap_nil, List.nil_append]
    exact epilogue_ok hp hD h
  | succ j ih =>
    intro hj s h
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine out_step hp hD (by omega) h fun s' h' => ?_
    rw [show 8 - (j + 1) + 1 = 8 - j by omega]
    exact ih (by omega) s' (by rwa [show 8 - (j + 1) + 1 = 8 - j by omega] at h')

/-- No instruction of `finalize` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs finalize, dstOf i ≠ some r := by
  have : ((instrs finalize).all fun i => untouched.all fun r => dstOf i != some r) = true := by
    decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.finalizeAArch64.post s₀ s' := by
  refine WP.mono (WP.gprs (Q := Post s₀) ?_ untouched_ok) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨⟨fun r hr => ?_, hsp⟩, hpost⟩
  · rw [finalize_eq]
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
    refine WP.seq (WP.mono (Q := Done s₀) ?_ fun sD hD => ?_)
    · refine WP.loop (M := isa) (fun i s => ∃ n, LInv s₀ i n s) ?_ k s₁ ⟨_, hL⟩
      rintro i s ⟨n, hL⟩
      refine WP.mono (body_ok hp hL) fun s' h => ?_
      rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
      · exact .inl ⟨he, hD⟩
      · exact .inr ⟨he, 0, by omega, 0, hL'⟩
    · have := out_all hp hD 8 le_rfl sD ⟨hD.1.rd, hD.1.wr, fun _ _ => rfl, rfl, by simp [writeBytes_nil]⟩
      rw [show 8 - 8 = 0 from rfl, List.drop_zero] at this
      exact this
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hu .x18 (by simp [untouched])
    · exact hsv (.x19, 112) (by simp [saved])
    · exact hsv (.x20, 120) (by simp [saved])
    · exact hsv (.x21, 128) (by simp [saved])
    · exact hsv (.x22, 136) (by simp [saved])
    · exact hsv (.x23, 144) (by simp [saved])
    · exact hsv (.x24, 152) (by simp [saved])
    all_goals exact hu _ (by simp [untouched])

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Spec.Sha256.finalizeAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree [.x0, .x1, .x2, .x3] s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 160⟩]

set_option maxHeartbeats 0 in
theorem finalize_verified : Verified AArch64.target finalize Spec.Sha256.finalizeAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) [.x0, .x1, .x2, .x3] (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha256.AArch64.Stream.Finalize
