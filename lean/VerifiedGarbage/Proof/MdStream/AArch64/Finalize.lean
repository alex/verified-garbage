import VerifiedGarbage.Proof.MdStream.AArch64.Common

/-!
# Streaming Merkle–Damgård hash functions on AArch64: `finalize`

Untrusted: everything here is checked by Lean. The functional correctness of
`finalize`, for any hash function (`Md`) whose code stores the length field
and writes the digest as `Shape` says, and any correct compression function
(`CalleeOk`). The same structure as the x86-64 proof
(`VG.Proof.MdStream.X86_64.Finalize`). Constant time is proven for each hash
function's code by the taint analysis, calls included.
-/

namespace VG.Proof.MdStream.AArch64.Finalize

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev out : Addr := s₀.gpr .x2
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨st s₀, P.N + 64⟩
abbrev outR : Region := ⟨out s₀, P.N⟩
abbrev scR : Region := ⟨scr s₀, P.so + 48⟩
/-- The buffer. -/
abbrev buf : Addr := st s₀ + BitVec.ofNat 64 P.N

end

section
variable {P : Params} (H : Md 64 P.N 8) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .x1 = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (64 - n) 0).getD t 0))
    (H.parse fun t => (List.replicate 56 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (56 - n) 0 ++ H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR P s₀, outR P s₀, scR P s₀]
  st_out : (stR P s₀).Disjoint (outR P s₀)
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  out_scr : (outR P s₀).Disjoint (scR P s₀)

/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 16, 16⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (P : Params) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR P s₀)
  out : (stkR s₀).Disjoint (outR P s₀)
  scr : (stkR s₀).Disjoint (scR P s₀)

theorem pre_of {P : Params} {H : Md 64 P.N 8} {s₀ : State} (h : (finK H).pre s₀) : Pre P s₀ ∧ Stack P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = out s₀
  x22 : s.gpr .x22 = s₀.gpr .x1
  sp : s.sp = s₀.sp
  frame : Frame [stR P s₀, scR P s₀] s₀.mem s.mem
  saved : Saved P (scr s₀) s₀.gpr s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (H : Md 64 P.N 8) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  x23 : s.gpr .x23 = BitVec.ofNat 64 n
  x24 : s.gpr .x24 = BitVec.ofNat 64 k
  hash : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then Fin1 H s₀ s.mem n m else Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md 64 P.N 8) (s₀ : State) (s : State) : Prop :=
  Common P s₀ s ∧ ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (st s₀))

section
variable {P : Params} {H : Md 64 P.N 8}

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem buf_add (s₀ : State) (n : Nat) : buf P s₀ + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (P.N + n) :=
  add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common P s₀ s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common P s₀ s' where
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
theorem saved_sub (hd : Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR P s₀) := by
  have := saved_offset hd hp; have := hd.so
  exact sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (h : Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [stR P s₀, scR P s₀] s₀.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Saved P (scr s₀) s₀.gpr (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N
  have hf : Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [buf_add]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hd hp')

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x24], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  x9 : s.gpr .x9 = 0
  x23 : s.gpr .x23 = BitVec.ofNat 64 (n + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sI : State} (hC : Common P s₀ sI)
    {n lim j : Nat} (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero P s₀ sI n lim j s) :
    WP isa (.block (zeroBody P)) s fun s' =>
      Zero P s₀ sI n lim (j + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (lim - n - (j + 1)) := by
  have := hd.N
  have hx19 : s.gpr .x19 = st s₀ := by rw [h.keep _ (by simp), hC.x19]
  have hout : InRegions s.wr (buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [add_ofNat, buf_add]
    exact contains_offset (by omega) (by omega)
  unfold zeroBody
  refine wp_add fun s₁ u₁ => wp_strb (a := buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega)
    ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19, h.x23, buf, BitVec.ofNat_add]
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

theorem zero_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sI : State} (hC : Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero P s₀ sI n lim 0 s) :
    WP isa (.ite (.zero .x .x11) (.block []) (.loop (.block (zeroBody P)) (.nonzero .x .x11))) s
      (Zero P s₀ sI n lim (lim - n)) := by
  have hz : eval (.zero .x .x11) s = some (decide (lim - n = 0)) := by
    rw [eval_zero, h.x11, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', h11⟩ => ?_
    have hz' : isa.eval (.nonzero .x .x11) s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x11) s' = _
      rw [eval_nonzero, h11, bne, ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {s : State} (hC : Common P s₀ s) (hx1 : s.gpr .x1 = buf P s₀) {Q : State → Prop}
    (hQ : ∀ s', Common P s₀ s' → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.blockAt s.mem (buf P s₀)) → Q s') :
    WP isa (compressAt name code) s Q := by
  have := hd.N; have := hd.so
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨buf P s₀, 64⟩ (stR P s₀) := sub_offset (off := P.N) (by omega) (by omega)
  refine compressAt_ok hf hC.x19 hC.x20 hx1 ((hp.st_scr.sub_left eN).sub_right eso) ?_
    ((hp.st_scr.sub_left eb).sub_right eso) ?_ ?_ fun s' hrd hwr hcs hsp hf' hstate =>
      hQ s' ?_ hcs hstate
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · have cs : ∀ r, r ∈ preserved → r ≠ .x30 → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide) (by decide)]; exact hC.x19,
      by rw [cs _ (by decide) (by decide)]; exact hC.x20,
      by rw [cs _ (by decide) (by decide)]; exact hC.x21,
      by rw [cs _ (by decide) (by decide)]; exact hC.x22, hsp.trans hC.sp, hC.frame.trans (hf'.sub ?_),
      fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR P s₀, by simp, eso⟩
    · rw [← hC.saved p hp']
      have := saved_offset hd hp'
      refine hf'.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ (by omega) (by omega)

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md 64 P.N 8) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval (.zero .x .x24) s = some false ∧ Done H s₀ s) ∨
    (eval (.zero .x .x24) s = some true ∧ k = 1 ∧ LInv H s₀ 0 0 s)

theorem body_ok (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {k n : Nat} {s : State} (h : LInv H s₀ k n s) :
    WP isa (finalizeBody P name code) s (Step H s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  have := hd.N
  unfold finalizeBody
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
  have hZ : Zero P s₀ s n (56 + 8 * k) 0 s₅ := by
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
  refine WP.seq (WP.mono (zero_ok hd hp hC (by omega) hn hZ) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hd hp (n := n) (xs := List.replicate (56 + 8 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.x19],
      by rw [hZ₆.keep _ (by simp), hC.x20], by rw [hZ₆.keep _ (by simp), hC.x21],
      by rw [hZ₆.keep _ (by simp), hC.x22], hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (st s₀) = H.stateAt s.mem (st s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [buf_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (buf P s₀) (56 + 8 * k) =
      bytesAt s.mem (buf P s₀) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h24₆ : s₆.gpr .x24 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.x24]
  -- In the last block, the length field.
  have hz₆ : eval (.zero .x .x24) s₆ = some (decide (k = 0)) := by
    rw [eval_zero, h24₆, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common P s₀ s₈ ∧ s₈.gpr .x24 = BitVec.ofNat 64 k ∧
      H.stateAt s₈.mem (st s₀) = H.stateAt s.mem (st s₀) ∧
      ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (buf P s₀) 64 = bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, h24₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₆ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have e : st s₀ + BitVec.ofNat 64 (P.N + 56) = buf P s₀ + BitVec.ofNat 64 56 := by rw [buf_add]
      have hout : InRegions s₆.wr (s₆.gpr .x19 + BitVec.ofNat 64 (P.N + 56)) 8 :=
        ⟨stR P s₀, by simp [hC₆.wr, hp.wr], by rw [hC₆.x19]; exact contains_offset (by omega) (by omega)⟩
      refine WP.mono (hs.len s₆ hout) fun s₈ ⟨g₈, rd₈, wr₈, sp₈, m₈⟩ => ?_
      rw [hC₆.x19, hC₆.x22, e] at m₈
      have hlen := H.lenOf_length (s₀.gpr .x1)
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hd hp (n := 56) (xs := H.lenOf (s₀.gpr .x1)) (by omega)
      refine ⟨⟨rd₈.trans hC₆.rd, wr₈.trans hC₆.wr, by rw [g₈ _ (by decide) (by decide), hC₆.x19],
        by rw [g₈ _ (by decide) (by decide), hC₆.x20], by rw [g₈ _ (by decide) (by decide), hC₆.x21],
        by rw [g₈ _ (by decide) (by decide), hC₆.x22], sp₈.trans hC₆.sp,
        by rw [m₈]; exact hfr, by rw [m₈]; exact hsv⟩,
        by rw [g₈ _ (by decide) (by decide), h24₆], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [buf_add]
        exact writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₆.mem (buf P s₀) 56 (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length] at e
        rw [m₈, e, hby₆, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₆, h24₆, hst₆, fun iv m _ _ => ?_⟩
      rw [hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_addImm (by omega) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common P s₀ s₉ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .x1 := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
      rw [u₉.other r this]) u₉.mem u₉.rd u₉.wr u₉.sp
  have hx1 : s₉.gpr .x1 = buf P s₀ := by rw [u₉.gpr, hC₈.x19]
  refine WP.seq (compress_buf hd hf hp hC₉ hx1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have h24₁₁ : s₁₁.gpr .x24 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide) (by decide), u₉.other _ (by decide), h24₈]
  have hblk : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₉.mem (buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₉.mem]
    exact bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine wp_movz fun s₁₂ u₁₂ => wp_subImm (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have hC₁₃ : Common P s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .x24 ∧ r ≠ .x23 := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr]) (by rw [u₁₃.sp, u₁₂.sp])
  have hz : eval (.zero .x .x24) s₁₃ = some (decide (k = 1)) := by
    rw [eval_zero, u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁, sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.parse fun t =>
        (bytesAt s.mem (buf P s₀) n ++
          (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk iv m hm hok, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [hz]; simp, hC₁₃, fun iv m hm hok => ?_⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (.block (finalizeStart P)) s₀ fun s => ∃ k, LInv H s₀ k (cnt s₀ % 64 + 1) s := by
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have := hd.N; have := hd.so
  refine save_ok hd (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hp.wr], contains_offset hd₂ (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_movz fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  have hm₇ : s₇.mem = saveMem P s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hC₇ : Common P s₀ s₇ := by
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
    · rw [hm₇]; exact (saveMem_frame hd _ _ _).mono (by simp)
    · rw [hm₇]; exact saveMem_saved hd _ _ _
  have hr23 : s₇.gpr .x23 = BitVec.ofNat 64 (cnt s₀ % 64) := by
    rw [u₇.gpr, u₆.other .x22 (by decide), u₆.gpr, u₅.gpr, u₄.other .x1 (by decide),
      u₃.other .x1 (by decide), u₂.other .x1 (by decide), g₁]
    exact and63 _
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) 1 := by
    refine ⟨stR P s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [buf_add]; exact contains_offset (by omega) (by omega)
  refine wp_movz fun s₈ u₈ => wp_add fun s₉ u₉ =>
    wp_strb (a := buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.x19, hr23, buf]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hd hp (n := cnt s₀ % 64) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₇.mem (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_addImm (by decide) fun s₁₁ u₁₁ => wp_addImm (by decide) fun s₁₂ u₁₂ =>
    wp_lsr (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .x23 → r ≠ .x24 → r ≠ .x9 → r ≠ .x12 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common P s₀ s₁₃ :=
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
  have hbytes : ∀ iv m, R₀ H s₀ iv m → bytesAt s₁₃.mem (buf P s₀) (cnt s₀ % 64 + 1) =
      Md.rest 64 m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₇.mem (buf P s₀) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := frame_bytes (saveMem_frame hd s₀.mem (scr s₀) s₀.gpr) (R := stR P s₀)
      (by simpa using hp.st_scr) (by show P.N + 64 ≤ 2 ^ 64; omega) (i := P.N + i)
      (by show P.N + i < P.N + 64; omega)
    rwa [← buf_add] at this
  have hstate : H.stateAt s₁₃.mem (st s₀) = H.stateAt s₀.mem (st s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, buf_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₇]
    exact frame_bytes (saveMem_frame hd s₀.mem (scr s₀) s₀.gpr) (R := stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + 64 ≤ 2 ^ 64; omega) (by show i < P.N + 64; omega)
  by_cases hb : 57 ≤ cnt s₀ % 64 + 1
  · have hk : (cnt s₀ % 64 + 8) / 64 = 1 := by omega
    refine ⟨1, hC₁₃, (Nat.le_refl _), by omega, hr23', by rw [hr24, hk], fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H (by decide) (by decide) (by rw [← hm.length]; omega), Fin1, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 64 - 1 - cnt s₀ % 64 by omega]
  · have hk : (cnt s₀ % 64 + 8) / 64 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr23', by rw [hr24, hk], fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H (by decide) (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 64 - 8 - 1 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md 64 P.N 8) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ (finK H).post s₀ s'

theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sD : State} (hD : Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .x9 → s.gpr r = sD.gpr r)
    (hsp : s.sp = sD.sp) (hm : s.mem = writeBytes sD.mem (out s₀) (H.digest (H.stateAt sD.mem (st s₀)))) :
    WP isa (.block (restore P)) s (Post P H s₀) := by
  have := hd.N; have := hd.so
  have hC := hD.1
  have hdl := H.digest_length (H.stateAt sD.mem (st s₀))
  have hfo : Frame [outR P s₀] sD.mem (writeBytes sD.mem (out s₀) (H.digest (H.stateAt sD.mem (st s₀)))) :=
    writeBytes_frame _ _ _ (by
      rw [show out s₀ = out s₀ + BitVec.ofNat 64 0 by simp]
      exact contains_offset (by omega) (by omega))
  refine restore_ok hd (scr := scr s₀) (by rw [hkeep _ (by decide), hC.x20])
    (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hrd, hwr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp' => ⟨hs, by rw [hsp', hsp, hC.sp], ?_⟩
  · rw [hm, ← hC.saved p hp']
    have := saved_offset hd hp'
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (saved_sub hd hp')
  · intro iv m hr hok hc
    have e := bytesAt_writeBytes sD.mem (out s₀) 0 (H.digest (H.stateAt sD.mem (st s₀))) (by omega)
    rw [hdl, show out s₀ + BitVec.ofNat 64 0 = out s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (out s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hmem, hm, e]
    exact (hD.2 iv m ⟨hr, hc⟩ hok).symm

/-- `finalize` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeMain P name code), dstOf i ≠ some r) {s₀ : State}
    (hp : Pre P s₀) :
    WP isa (finalizeMain P name code) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ (finK H).post s₀ s' := by
  have := hd.N
  refine WP.mono (WP.gprs (Q := Post P H s₀) ?_ hu) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨preserved_of hsv hu, hsp, hpost⟩
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done H s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv H s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    rw [WP.block_append_iff]
    refine WP.mono (hs.out sD ?_ ?_ ?_) fun s ⟨g, rd, wr, sp, m⟩ =>
      epilogue_ok hd hp hD (rd.trans hC.rd) (wr.trans hC.wr) g sp (by rw [m, hC.x21, hC.x19])
    · refine ⟨stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.x19]; simpa using contains_offset (base := st s₀) (off := 0) (n := P.N) (len := P.N + 64)
        (by omega) (by omega)
    · refine ⟨outR P s₀, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.x21]; simpa using contains_offset (base := out s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hC.x19, hC.x21]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

/-- The state `finalizeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeMain P name code), dstOf i ≠ some r)
    (hn : 16 * (finalizeMain P name code).fdepth + 16 < 2 ^ 64) {s₀ : State} (hp : Pre P s₀)
    (hst : Stack P s₀) :
    WP isa (finalize P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finK H).post s₀ s' := by
  have hpi : Pre P (inner s₀) := ⟨hp.rd, hp.wr, hp.st_out, hp.st_scr, hp.out_scr⟩
  refine WP.frameReg hst.sp16 (fun R hR => ?_)
    (WP.mono (correctMain hd hs hf hu hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_) hn
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hst.st
    · exact hst.out
    · exact hst.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun iv m hm hok hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · exact hpost iv m (H.repr_congr (by decide) (fun i hi => write_frame_bytes (R := stR P s₀) hst.st
        (by have := hd.N; show P.N + 64 < 2 ^ 64; omega) hi) hm) hok hc

/-- A state satisfying the precondition. -/
def sat (P : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, P.N + 64⟩, ⟨0x2000, P.N⟩, ⟨0x3000, P.so + 48⟩]

/-- `finalize` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code), never writes `untouched`, and
fits its frames in the address space. -/
theorem verified (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hct : ConstantTime isa (finK H).pre (finK H).pub (finalize P name code))
    (hu : ((instrs (finalizeMain P name code)).all fun i => untouched.all fun r => dstOf i != some r) = true)
    (hn : 16 * (finalizeMain P name code).fdepth + 16 < 2 ^ 64) :
    Verified AArch64.target (finalize P name code) (finK H) := by
  have := hd.N; have := hd.so
  have hu' : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeMain P name code), dstOf i ≠ some r := by
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp hu i hi) r hr
    simpa using this
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hs hf hu' hn (pre_of hs').1 (pre_of hs').2
    exact ⟨t, s', he, h⟩
  · refine ⟨sat P, rfl, rfl, ?_, ?_, ?_, by simp only [sat]; decide, ?_, ?_, ?_⟩
    all_goals try simp only [sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

/-- The initial taint agrees on the public arguments. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (finK H).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

end

end VG.Proof.MdStream.AArch64.Finalize
