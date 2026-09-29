import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `finalize`

Untrusted: everything here is checked by Lean. The functional correctness of
`finalize`, for any hash function (`Md`) whose code stores the length field
and writes the digest as `Shape` says, and any correct compression function
(`CalleeOk`).
-/

namespace VG.Proof.MdStream.X86_64.Finalize

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame writeBytes_append bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev out : Addr := s₀.gpr .rdx
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, P.N + P.B⟩
abbrev outR : Region := ⟨out s₀, P.N⟩
abbrev scR : Region := ⟨scr s₀, P.so + 48⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The buffer. -/
abbrev buf : Addr := st s₀ + BitVec.ofNat 64 P.N

/-- The end of the zeros in a block: before the length field in the last
block (`k = 0`). -/
def lim (k : Nat) : Nat := if k = 0 then P.B - P.L else P.B

end

section
variable {P : Params} (H : Md P.B P.N P.L) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .rsi = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (P.B - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (P.B - P.L) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (P.B - P.L - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR P s₀, outR P s₀, scR P s₀]
  st_out : (stR P s₀).Disjoint (outR P s₀)
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  out_scr : (outR P s₀).Disjoint (scR P s₀)
  ret_st : (retR s₀).Disjoint (stR P s₀)
  ret_out : (retR s₀).Disjoint (outR P s₀)
  ret_scr : (retR s₀).Disjoint (scR P s₀)
  stk_st : (stkR s₀).Disjoint (stR P s₀)
  stk_out : (stkR s₀).Disjoint (outR P s₀)
  stk_scr : (stkR s₀).Disjoint (scR P s₀)

theorem pre_of {P : Params} {H : Md P.B P.N P.L} {s₀ : State} (h : (finK H).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega)
  rwa [BitVec.sub_add_cancel] at this

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rbp : s.gpr .rbp = out s₀
  r12 : s.gpr .r12 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [stR P s₀, scR P s₀, stkR s₀] s₀.mem s.mem
  saved : Saved P s₀ .rcx s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ lim P k
  r13 : s.gpr .r13 = BitVec.ofNat 64 n
  r14 : s.gpr .r14 = BitVec.ofNat 64 k
  hash : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then Fin1 H s₀ s.mem n m else Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  Common P s₀ s ∧ ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (st s₀))

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem lim_le (k : Nat) : lim P k ≤ P.B := by unfold lim; split <;> omega
theorem lim_ge (k : Nat) : P.B - P.L ≤ lim P k := by unfold lim; split <;> omega

theorem buf_add (s₀ : State) (n : Nat) : buf P s₀ + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (P.N + n) :=
  add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common P s₀ s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common P s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`. -/
theorem Common.writeBuf (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (h : Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ P.B) :
    Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [stR P s₀, scR P s₀, stkR s₀] s₀.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Saved P s₀ .rcx (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N; have := hd.B; have := hd.so
  have hf : Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [buf_add]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  have hd' := saved_offset hd hp'
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)))

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp, .r14], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  r9 : s.gpr .r9 = 0
  r13 : s.gpr .r13 = BitVec.ofNat 64 (n + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sI : State} (hC : Common P s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ P.B) (hj : j < lim - n) {s : State} (h : Zero P s₀ sI n lim j s) :
    WP isa (.block [.store8 (bufByte P) .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) s fun s' =>
      Zero P s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have := hd.N; have := hd.B
  have hrbx : s.gpr .rbx = st s₀ := by rw [h.keep _ (by simp), hC.rbx]
  have hout : InRegions s.wr (buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [add_ofNat, buf_add]
    exact contains_offset (by omega) (by omega)
  refine wp_store8 (r := .r9) (a := buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_ hout
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  · simp only [State.ea, bufByte, buf, hrbx, h.r13, BitVec.ofNat_add, BitVec.mul_one, ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ hz₃ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₃.rd, u₂.rd, rd₁, h.rd], by rw [u₃.wr, u₂.wr, wr₁, h.wr], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .rax ∧ r ≠ .r13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other r this.1, u₂.other r this.2, g₁, h.keep r hr]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.r9]
  · rw [u₃.other _ (by decide), u₂.gpr, g₁, h.r13, sx1, ← Nat.add_assoc, ofNat_succ]
  · rw [u₃.gpr, u₂.other _ (by decide), g₁, h.rax, sx1, ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₃.mem, u₂.mem, m₁, h.r9, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₃, u₂.other _ (by decide), g₁, h.rax, sx1, ofNat_pred (by omega), ofNat_beq_zero (by omega),
      Nat.sub_sub, Nat.sub_sub]

theorem zero_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sI : State} (hC : Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State} (h : Zero P s₀ sI n lim 0 s)
    (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (zeroLoop P)) s (Zero P s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by simp [eval, hz', hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The call of the compression function's requirements. -/
theorem Common.callOk (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (hC : Common P s₀ s)
    (hrsi : s.gpr .rsi = buf P s₀) : CallOk P s (st s₀) (scr s₀) (buf P s₀) := by
  have := hd.N; have := hd.B; have := hd.so
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨buf P s₀, P.B⟩ (stR P s₀) := sub_offset (off := P.N) (by omega) (by omega)
  have hsp := hC.rsp
  refine ⟨hC.rbx, hC.r15, hrsi, (hp.st_scr.sub_left eN).sub_right eso, ?_,
    (hp.st_scr.sub_left eb).sub_right eso, by rw [hsp]; exact hp.stk_st.sub_right eN,
    by rw [hsp]; exact hp.stk_scr.sub_right eso, by rw [hsp]; exact hp.stk_st.sub_right eb, ?_, ?_⟩
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

/-- The compression of the buffer. -/
theorem compress_buf (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {s : State} (hC : Common P s₀ s) (hrsi : s.gpr .rsi = buf P s₀) {Q : State → Prop}
    (hQ : ∀ s', Common P s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.blockAt s.mem (buf P s₀)) →
      s'.gpr .rdi = st s₀ → s'.gpr .rcx = scr s₀ → Q s') :
    WP isa (compressAt name code) s Q := by
  have := hd.N; have := hd.B; have := hd.so
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega)
  have hsp := hC.rsp
  refine compressAt_ok H hf (hC.callOk hd hp hrsi) (by omega) (by omega)
    fun s' hrd hwr hcs hf hstate hdi hcx => hQ s' ?_ hcs hstate hdi hcx
  have cs : ∀ r, r ∈ calleeSaved → s'.gpr r = s.gpr r := hcs
  refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.rbx,
    by rw [cs _ (by decide)]; exact hC.r15, by rw [cs _ (by decide)]; exact hC.rbp,
    by rw [cs _ (by decide)]; exact hC.r12, by rw [cs _ (by decide)]; exact hC.rsp,
    hC.frame.trans (hf.sub ?_), fun p hp' => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, eN⟩
    · exact ⟨scR P s₀, by simp, eso⟩
    · exact ⟨stkR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
  · rw [← hC.saved p hp']
    have hd' := saved_offset hd hp'
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_
      (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))).sub_right eN
    · rw [ofInt_natCast]; exact Offset.disjoint_base _ hd'.1 (by omega)
    · rw [hsp]
      exact hp.stk_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))

end

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (k = 0 ∧ eval .e s = some false ∧ Done H s₀ s ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rcx = scr s₀) ∨
    (k = 1 ∧ eval .e s = some true ∧ LInv H s₀ 0 0 s)

/-- Before the call of the compression function: the block to compress is
ready in the buffer, and compressing it finishes the iteration. -/
def Mid {P : Params} (H : Md P.B P.N P.L) (name : String) (code : Prog isa) (s₀ : State) (k : Nat)
    (s : State) : Prop :=
  Common P s₀ s ∧ s.gpr .rsi = buf P s₀ ∧
    WP isa (.seq (compressAt name code) (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)])) s
      (Step H s₀ k)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pad_ok (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {k n : Nat} {s : State} (h : LInv H s₀ k n s) :
    WP isa (finalizePad P) s (Mid H name code s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  have := hd.N; have := hd.B; have := hd.L
  have hlim := lim_le (P := P) k; have hlim' := lim_ge (P := P) k
  unfold finalizePad
  -- `rax := B` or `B - L`: the end of the zeros.
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_test fun s₂ g₂ m₂ rd₂ wr₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.r14, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hne : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], r ≠ .rax := by decide
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (lim P k) ∧
      (∀ r, r ≠ .rax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨hrax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.gpr, zx_ofNat (by omega)]; rfl
      · rw [u₃.other r hr, g₂, u₁.other r hr]
      · rw [u₃.mem, m₂, u₁.mem]
      · rw [u₃.rd, rd₂, u₁.rd]
      · rw [u₃.wr, wr₂, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [g₂, u₁.gpr, zx_ofNat (by omega)]; simp [lim, hb]
      · rw [g₂, u₁.other r hr]
      · rw [m₂, u₁.mem]
      · rw [rd₂, u₁.rd]
      · rw [wr₂, u₁.wr]
  -- Zero the rest of the buffer, up to `lim`.
  have hC₃ : Common P s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (hne r hr)) m₃ rd₃ wr₃
  refine WP.seq (wp_mov32i fun s₄ u₄ _ _ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hrax₅ : s₅.gpr .rax = BitVec.ofNat 64 (lim P k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.other _ (by decide), hrax₃, g₃ _ (by decide), h.r13,
      sub_ofNat (by omega)]
  have hZ : Zero P s₀ s n (lim P k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .rax ∧ r ≠ .r9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r13, Nat.add_zero]
    · rw [hrax₅, Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  have hz₅ : s₅.zf = some (decide (lim P k - n = 0)) := by
    rw [z₅, ← u₅.gpr, hrax₅, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (zero_ok hd hp hC hlim hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hd hp (n := n) (xs := List.replicate (lim P k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.rbx],
      by rw [hZ₆.keep _ (by simp), hC.r15], by rw [hZ₆.keep _ (by simp), hC.rbp],
      by rw [hZ₆.keep _ (by simp), hC.r12], by rw [hZ₆.keep _ (by simp), hC.rsp],
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (st s₀) = H.stateAt s.mem (st s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [buf_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (buf P s₀) (lim P k) =
      bytesAt s.mem (buf P s₀) n ++ List.replicate (lim P k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h14₆ : s₆.gpr .r14 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.r14]
  -- In the last block, the length field.
  refine WP.seq (wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_)
  have hC₇ : Common P s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [g₇]) m₇ rd₇ wr₇
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, h14₆, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common P s₀ s₈ ∧ s₈.gpr .r14 = BitVec.ofNat 64 k ∧
      H.stateAt s₈.mem (st s₀) = H.stateAt s.mem (st s₀) ∧
      ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (buf P s₀) P.B = bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++
          H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, h14₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have e : st s₀ + BitVec.ofNat 64 (P.N + P.B - P.L) = buf P s₀ + BitVec.ofNat 64 (P.B - P.L) := by
        rw [buf_add, show P.N + (P.B - P.L) = P.N + P.B - P.L by omega]
      have hout : InRegions s₇.wr (s₇.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
        ⟨stR P s₀, by simp [hC₇.wr, hp.wr], by rw [hC₇.rbx]; exact contains_offset (by omega) (by omega)⟩
      refine WP.mono (hs.len s₇ hout) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      rw [hC₇.rbx, hC₇.r12, e] at m₈
      have hlen := H.lenOf_length (s₀.gpr .rsi)
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hd hp (n := P.B - P.L) (xs := H.lenOf (s₀.gpr .rsi)) (by omega)
      have hl0 : lim P 0 = P.B - P.L := rfl
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide), hC₇.rbx],
        by rw [g₈ _ (by decide), hC₇.r15], by rw [g₈ _ (by decide), hC₇.rbp], by rw [g₈ _ (by decide), hC₇.r12],
        by rw [g₈ _ (by decide), hC₇.rsp], by rw [m₈, m₇]; exact hfr, by rw [m₈, m₇]; exact hsv⟩,
        by rw [g₈ _ (by decide), g₇, h14₆], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, m₇, ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [buf_add]
        exact writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₆.mem (buf P s₀) (P.B - P.L) (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length, show P.B - P.L + P.L = P.B by omega] at e
        rw [m₈, m₇, e, ← hl0, hby₆, hl0, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, by rw [g₇, h14₆], by rw [m₇, hst₆], fun iv m _ _ => ?_⟩
      have e1 : lim P 1 = P.B := rfl
      rw [e1] at hby₆
      rw [m₇, hby₆]; simp
  -- Compress the block.
  refine wp_mov fun s₉ u₉ _ _ => wp_addi fun s₁₀ u₁₀ => WP.block_nil ?_
  have hC₁₀ : Common P s₀ s₁₀ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .rsi := by simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [u₁₀.other r this, u₉.other r this]) (by rw [u₁₀.mem, u₉.mem]) (by rw [u₁₀.rd, u₉.rd])
    (by rw [u₁₀.wr, u₉.wr])
  have hrsi : s₁₀.gpr .rsi = buf P s₀ := by
    rw [u₁₀.gpr, u₉.gpr, hC₈.rbx, sx_ofNat (by omega)]
  refine ⟨hC₁₀, hrsi, ?_⟩
  refine WP.seq (compress_buf hd hf hp hC₁₀ hrsi fun s₁₁ hC₁₁ cs₁₁ hst₁₁ hdi₁₁ hcx₁₁ => ?_)
  have h14₁₁ : s₁₁.gpr .r14 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h14₈]
  have hblk : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₁₀.mem (buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (buf P s₀) n ++ (if k = 1 then List.replicate (P.B - n) 0 else
        List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₁₀.mem, u₉.mem]
    exact bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine wp_mov32i fun s₁₂ u₁₂ _ _ => wp_subi fun s₁₃ u₁₃ z₁₃ => WP.block_nil ?_
  have hC₁₃ : Common P s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .r14 ∧ r ≠ .r13 := by simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr])
  have hz : s₁₃.zf = some (decide (k = 1)) := by
    rw [z₁₃, u₁₂.other _ (by decide), h14₁₁, sx1, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.parse fun t =>
        (bytesAt s.mem (buf P s₀) n ++ (if k = 1 then List.replicate (P.B - n) 0 else
          List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₁₀.mem, u₉.mem, hst₈, ← hblk iv m hm hok, u₁₀.mem, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨rfl, by simp [eval, hz], ⟨hC₁₃, by omega, by rw [lim]; simp, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h14₁₁, sx1]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨rfl, by simp [eval, hz], ⟨hC₁₃, fun iv m hm hok => ?_⟩,
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), hdi₁₁],
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), hcx₁₁]⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

theorem body_ok (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {k n : Nat} {s : State} (h : LInv H s₀ k n s) :
    WP isa (finalizeBody P name code) s (Step H s₀ k) :=
  WP.seq (WP.mono (pad_ok hd hs hf hp h) fun _ h => h.2.2)

/-! ## Prologue -/

theorem R₀.length (hd : Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) :
    cnt s₀ % P.B = m.length % P.B := by
  rw [cnt, h.2, BitVec.toNat_ofNat, hd.mod]

/-- The number of blocks after the first, `1` if the length field does not
fit in the first. -/
def kOf (P : Params) (s₀ : State) : Nat := if P.B - P.L + 1 ≤ cnt s₀ % P.B + 1 then 1 else 0

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (finalizeStart P) s₀ (LInv H s₀ (kOf P s₀) (cnt s₀ % P.B + 1)) := by
  have := hd.N; have := hd.B; have := hd.L; have := hd.so
  have o : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR P s₀, by simp [hp.wr], contains_offset' hd (by omega)⟩
  have hr : cnt s₀ % P.B < P.B := Nat.mod_lt _ hd.pos
  have hr' : (s₀.gpr .rsi).toNat % P.B < P.B := hr
  unfold finalizeStart
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) rfl (o _ (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_)
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o _ (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int))
    (by simp only [State.ea, at_, g₂, g₁]) (by rw [wr₂, wr₁]; exact o _ (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o _ (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have hg₆ : s₆.gpr = s₀.gpr := by rw [g₆, g₅, g₄, g₃, g₂, g₁]
  have hm₆ : s₆.mem = saveMem P s₀ .rcx := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [saveMem, g₅, g₄, g₃, g₂, g₁]
  have hsf := saveMem_frame (s₀ := s₀) (b := .rcx) hd
  refine wp_mov fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ =>
    wp_mov fun s₁₁ u₁₁ _ _ => wp_andi fun s₁₂ u₁₂ => ?_
  have hC₁₂ : Common P s₀ s₁₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
    · rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.gpr, hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.gpr, u₇.other _ (by decide), hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
        u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
      exact hsf.mono (by simp)
    · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]; exact saveMem_saved hd
  have hm₁₂ : s₁₂.mem = saveMem P s₀ .rcx := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  have hr13 : s₁₂.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % P.B) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), hg₆]
    exact and_mask hd.B _
  -- The `0x80` byte.
  have hout : InRegions s₁₂.wr (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % P.B)) 1 := by
    refine ⟨stR P s₀, by simp [hC₁₂.wr, hp.wr], ?_⟩
    rw [buf_add]; exact contains_offset (by omega) (by omega)
  refine wp_mov32i fun s₁₃ u₁₃ _ _ => wp_store8 (a := buf P s₀ + BitVec.ofNat 64 (cnt s₀ % P.B)) ?_
    (by rw [u₁₃.wr]; exact hout) fun s₁₄ g₁₄ m₁₄ rd₁₄ wr₁₄ => ?_
  · simp only [State.ea, bufByte, u₁₃.other .rbx (by decide), u₁₃.other .r13 (by decide), hC₁₂.rbx, hr13,
      BitVec.mul_one, ofInt_natCast, buf]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₁₂.writeBuf hd hp (n := cnt s₀ % P.B) (xs := [0x80]) (by simp; omega)
  have hm₁₄ : s₁₄.mem = writeBytes s₁₂.mem (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % P.B)) [0x80] := by
    rw [m₁₄, u₁₃.mem, u₁₃.gpr, ← List.nil_append [(0x80 : Byte)], writeBytes_snoc _ _ _ _ (by simp),
      writeBytes_nil]
    simp
  refine wp_addi fun s₁₅ u₁₅ => wp_mov32i fun s₁₆ u₁₆ _ _ => wp_cmpi fun s₁₇ g₁₇ m₁₇ rd₁₇ wr₁₇ cf₁₇ _ =>
    WP.block_nil ?_
  have keep : ∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .rax → s₁₇.gpr r = s₁₂.gpr r := fun r h1 h2 h3 => by
    rw [g₁₇, u₁₆.other r h2, u₁₅.other r h1, g₁₄, u₁₃.other r h3]
  have hm₁₇ : s₁₇.mem = s₁₄.mem := by rw [m₁₇, u₁₆.mem, u₁₅.mem]
  have hC₁₇ : Common P s₀ s₁₇ :=
    ⟨by rw [rd₁₇, u₁₆.rd, u₁₅.rd, rd₁₄, u₁₃.rd, hC₁₂.rd], by rw [wr₁₇, u₁₆.wr, u₁₅.wr, wr₁₄, u₁₃.wr, hC₁₂.wr],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rbx],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.r12],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rsp],
      by rw [hm₁₇, hm₁₄]; exact hfr, by rw [hm₁₇, hm₁₄]; exact hsv⟩
  have hr13' : s₁₇.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % P.B + 1) := by
    rw [g₁₇, u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, u₁₃.other _ (by decide), hr13, sx1, ofNat_succ]
  have hcf : s₁₇.cf = some (decide (cnt s₀ % P.B + 1 < P.B - P.L + 1)) := by
    rw [cf₁₇, u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, u₁₃.other _ (by decide), hr13, sx1, ← ofNat_succ,
      sx_ofNat (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := cnt s₀ % P.B + 1) (by omega), Nat.mod_eq_of_lt (a := P.B - P.L + 1) (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ H s₀ iv m → bytesAt s₁₇.mem (buf P s₀) (cnt s₀ % P.B + 1) =
      Md.rest P.B m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₁₂.mem (buf P s₀) (cnt s₀ % P.B) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₇, hm₁₄, e, hm₁₂]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length hd]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := Nat.mod_lt m.length hd.pos
    have := hsf.bytes (R := stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega)
      (i := P.N + i) (by show P.N + i < P.N + P.B; omega)
    rwa [← buf_add] at this
  have hstate : H.stateAt s₁₇.mem (st s₀) = H.stateAt s₀.mem (st s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₇, hm₁₄, buf_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₁₂]
    exact hsf.bytes (R := stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega)
      (by show i < P.N + P.B; omega)
  refine WP.ite (!decide (cnt s₀ % P.B + 1 < P.B - P.L + 1)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    rw [show kOf P s₀ = 1 from ite_eq_left_iff.mpr fun h => absurd hb h]
    refine wp_mov32i fun s₁₈ u₁₈ _ _ => WP.block_nil ⟨hC₁₇.of_gpr (fun r hr => u₁₈.other r (by
      simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide)) u₁₈.mem u₁₈.rd u₁₈.wr,
      (Nat.le_refl _), by rw [lim]; simp; omega, by rw [u₁₈.other _ (by decide), hr13'],
      by rw [u₁₈.gpr]; rfl, fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H hd.pos (by omega) (by rw [← hm.length hd]; omega), Fin1, u₁₈.mem, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length hd, show P.B - (cnt s₀ % P.B + 1) = P.B - 1 - cnt s₀ % P.B by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    rw [show kOf P s₀ = 0 from ite_eq_right_iff.mpr fun h => absurd hb (by omega)]
    refine WP.block_nil ⟨hC₁₇, by omega, by rw [lim]; simp; omega, hr13', ?_, fun iv m hm _ => ?_⟩
    · rw [g₁₇, u₁₆.gpr]; rfl
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H hd.pos (by rw [← hm.length hd]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length hd, show P.B - P.L - (cnt s₀ % P.B + 1) = P.B - P.L - 1 - cnt s₀ % P.B by omega]

/-! ## Output and epilogue -/

set_option simprocs false in
theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {sD : State} (hD : Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .rax → s.gpr r = sD.gpr r)
    (hm : s.mem = writeBytes sD.mem (out s₀) (H.digest (H.stateAt sD.mem (st s₀))))
    (hdi : s.gpr .rdi = s₀.gpr .rdi) (hcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa (.block (restore P)) s fun s' =>
      gprPreserved s₀ s' ∧ (finK H).post s₀ s' ∧ s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  have := hd.N; have := hd.so
  have hC := hD.1
  have hdl := H.digest_length (H.stateAt sD.mem (st s₀))
  have hfo : Frame [outR P s₀] sD.mem (writeBytes sD.mem (out s₀) (H.digest (H.stateAt sD.mem (st s₀)))) :=
    writeBytes_frame _ _ _ (by
      rw [show out s₀ = out s₀ + BitVec.ofNat 64 0 by simp]
      exact contains_offset (by omega) (by omega))
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR P s₀, by simp [hrd, hwr, hp.wr], contains_offset' hd (by omega)⟩
  have sv : ∀ r d, (r, d) ∈ saved P →
      s.mem.readW (scr s₀ + BitVec.ofInt 64 ((d : Nat) : Int)) 64 = s₀.gpr r := by
    intro r d hrd
    rw [hm, ← hC.saved _ hrd]
    have hd' := saved_offset hd hrd
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (d : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact (hp.out_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)))
  have i0 := i P.so (by omega); have i1 := i (P.so + 8) (by omega); have i2 := i (P.so + 16) (by omega)
  have i3 := i (P.so + 24) (by omega); have i4 := i (P.so + 32) (by omega); have i5 := i (P.so + 40) (by omega)
  have g0 := sv .rbx P.so (by simp [saved]); have g1 := sv .rbp (P.so + 8) (by simp [saved])
  have g2 := sv .r12 (P.so + 16) (by simp [saved]); have g3 := sv .r13 (P.so + 24) (by simp [saved])
  have g4 := sv .r14 (P.so + 32) (by simp [saved]); have g5 := sv .r15 (P.so + 40) (by simp [saved])
  have hr15 : s.gpr .r15 = scr s₀ := by rw [hkeep _ (by decide), hC.r15]
  have hrsp : s.gpr .rsp = s₀.gpr .rsp := by rw [hkeep _ (by decide), hC.rsp]
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
    rw [hm, hfo.readW (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    exact hC.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk s₀⟩)
      (by decide)
  have hout : bytesAt s.mem (s₀.gpr .rdx) P.N = H.digest (H.stateAt sD.mem (st s₀)) := by
    have e := bytesAt_writeBytes sD.mem (out s₀) 0 (H.digest (H.stateAt sD.mem (st s₀))) (by omega)
    rw [hdl, show out s₀ + BitVec.ofNat 64 0 = out s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (out s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hm]; exact e
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun iv m hm' hok hc => ?_, hdi, hcx⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · rw [hout]; exact (hD.2 iv m ⟨hm', hc⟩ hok).symm

/-- `finalize` is correct, and leaves `rdi` and `rcx` as they were (which code
inlining it relies on). -/
theorem correct (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) :
    WP isa (finalize P name code) s₀ fun s' => gprPreserved s₀ s' ∧ (finK H).post s₀ s' ∧
      s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  have := hd.N; have := hd.B
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ hL => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => Done H s₀ s ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rcx = scr s₀) ?_
    fun sD ⟨hD, hdi, hcx⟩ => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv H s₀ i n s) ?_ (kOf P s₀) s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨-, he, hD⟩ | ⟨rfl, he, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    rw [WP.block_append_iff]
    refine WP.mono (hs.out sD ?_ ?_ ?_) fun s ⟨g, rd, wr, m⟩ =>
      epilogue_ok hd hp hD (rd.trans hC.rd) (wr.trans hC.wr) g (by rw [m, hC.rbp, hC.rbx])
        (by rw [g _ (by decide), hdi]) (by rw [g _ (by decide), hcx])
    · refine ⟨stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.rbx]; simpa using contains_offset (base := st s₀) (off := 0) (n := P.N) (len := P.N + P.B)
        (by omega) (by omega)
    · refine ⟨outR P s₀, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.rbp]; simpa using contains_offset (base := out s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hC.rbx, hC.rbp]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

/-- A state satisfying the precondition. -/
def sat (P : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, P.N⟩, ⟨0x3000, P.so + 48⟩]

/-- `finalize` is verified if it is constant time (`FinalizeCT.lean`) and
never loads MXCSR. -/
theorem verified_of (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (finK H).pre (finK H).pub (finalize P name code)) :
    Verified X86_64.target (finalize P name code) (finK H) := by
  have := hd.N; have := hd.B; have := hd.so
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hs hf (pre_of hs')
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2.1⟩
  · refine ⟨sat P, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

end

end VG.Proof.MdStream.X86_64.Finalize
