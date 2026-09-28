import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Update

/-!
# Streaming SHA-256 on x86-64: `finalize`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.X86_64.Stream.Finalize

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset contains_offset' toNat_ofNat_lt readW_writeW_save
  sub_offset ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream.Update (sub_ofNat sub_beq ofNat_beq_zero ofNat_succ ofNat_pred
  bytesAt_getD and63)
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev out : Addr := s₀.gpr .rdx
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 32⟩
abbrev scR : Region := ⟨scr s₀, 160⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha256.Repr s₀.mem (st s₀) m ∧ s₀.gpr .rsi = BitVec.ofNat 64 m.length

/-- The caller's callee-saved registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofInt 64 (p.2 : Int)) 64 = s₀.gpr p.1

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
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Spec.Sha256.finalizeX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rbp : s.gpr .rbp = out s₀
  r12 : s.gpr .r12 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  r13 : s.gpr .r13 = BitVec.ofNat 64 n
  r14 : s.gpr .r14 = BitVec.ofNat 64 k
  hash : ∀ m, R₀ s₀ m → Spec.Sha256.hash m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ m, R₀ s₀ m → Spec.Sha256.hash m = (stateAt s.mem (st s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ s' where
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
theorem Common.writeBuf {s₀ : State} (hp : Pre s₀) {s : State} (h : Common s₀ s) {n : Nat} {xs : List Byte}
    (hn : n + xs.length ≤ 64) :
    Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) ∧
      Frame [stR s₀, scR s₀] s₀.mem (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) := by
  have hf : Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 32 + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [show st s₀ + 32 + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (32 + n) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]
    exact contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  simp only [Impl.Sha256.X86_64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)))

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp, .r14], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  r9 : s.gpr .r9 = 0
  r13 : s.gpr .r13 = BitVec.ofNat 64 (n + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (st s₀ + 32 + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block [.store8 bufByte .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have hrbx : s.gpr .rbx = st s₀ := by rw [h.keep _ (by simp), hC.rbx]
  have hout : InRegions s.wr (st s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show st s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = st s₀ + BitVec.ofNat 64 (32 + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  refine wp_store8 (r := .r9) (a := st s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_ hout
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  · simp only [State.ea, bufByte, hrbx, h.r13, BitVec.ofNat_add, BitVec.mul_one,
      show BitVec.ofInt 64 32 = 32 from rfl]
    ac_rfl
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ hz₃ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₃.rd, u₂.rd, rd₁, h.rd], by rw [u₃.wr, u₂.wr, wr₁, h.wr], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .rax ∧ r ≠ .r13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other r this.1, u₂.other r this.2, g₁, h.keep r hr]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.r9]
  · rw [u₃.other _ (by decide), u₂.gpr, g₁, h.r13, e1, ← Nat.add_assoc, ofNat_succ]
  · rw [u₃.gpr, u₂.other _ (by decide), g₁, h.rax, e1, ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₃.mem, u₂.mem, m₁, h.r9, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₃, u₂.other _ (by decide), g₁, h.rax, e1, ofNat_pred (by omega), ofNat_beq_zero (by omega),
      Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre s₀) {sI : State} (hC : Common s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s)
    (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (.loop (.block [.store8 bufByte .r9, .alu .add .r13 (.imm 1),
      .alu .sub .rax (.imm 1)]) .ne)) s (Zero s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by simp [eval, hz', hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

theorem len_bits {m : List Byte} {x : BitVec 64} (hx : x = BitVec.ofNat 64 m.length) :
    BitVec.ofNat 64 (8 * x.toNat) = BitVec.ofNat 64 (8 * m.length) := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

theorem st_add (s₀ : State) (n : Nat) :
    st s₀ + 32 + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (32 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-- The inlined compression of the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre s₀) {s : State} (hC : Common s₀ s)
    (hrsi : s.gpr .rsi = st s₀ + 32) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (st s₀) = compress (stateAt s.mem (st s₀)) (blockAt s.mem (st s₀ + 32)) →
      s'.gpr .rdi = st s₀ → s'.gpr .rcx = scr s₀ → Q s') :
    WP isa compressAt s Q := by
  have e32 : Region.Sub ⟨st s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scr s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨st s₀ + 32, 64⟩ (stR s₀) := sub_offset (off := 32) (by omega) (by omega)
  have hsp := hC.rsp
  refine compressAt_ok hC.rbx hC.r15 hrsi ((hp.st_scr.sub_left e32).sub_right e112) ?_
    ((hp.st_scr.sub_left eb).sub_right e112) (hsp ▸ (hp.ret_st.sub_right e32))
    (hsp ▸ (hp.ret_scr.sub_right e112)) ?_ ?_ fun s' hrd hwr hcs hf hstate hdi hcx =>
      hQ s' ?_ hcs hstate hdi hcx
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
  · have cs : ∀ r, r ∈ calleeSaved → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.rbx,
      by rw [cs _ (by decide)]; exact hC.r15, by rw [cs _ (by decide)]; exact hC.rbp,
      by rw [cs _ (by decide)]; exact hC.r12, by rw [cs _ (by decide)]; exact hC.rsp,
      hC.frame.trans (hf.sub ?_), fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
    · rw [← hC.saved p hp']
      simp only [Impl.Sha256.X86_64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 160 := by rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))).sub_right e32
      · intro a h₁ h₂; simp only [Region.Contains, ofInt_natCast] at h₁ h₂; bv_omega

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval .e s = some false ∧ Done s₀ s ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rcx = scr s₀) ∨ (eval .e s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

set_option maxHeartbeats 1000000 in
theorem body_ok {s₀ : State} (hp : Pre s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s (Step s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  unfold finalizeBody
  -- `rax := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => wp_test fun s₂ g₂ m₂ rd₂ wr₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.r14, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hne : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], r ≠ .rax := by decide
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (56 + 8 * k) ∧
      (∀ r, r ≠ .rax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨hrax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.other r hr, g₂, u₁.other r hr]
      · rw [u₃.mem, m₂, u₁.mem]
      · rw [u₃.rd, rd₂, u₁.rd]
      · rw [u₃.wr, wr₂, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [g₂, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [g₂, u₁.other r hr]
      · rw [m₂, u₁.mem]
      · rw [rd₂, u₁.rd]
      · rw [wr₂, u₁.wr]
  -- Zero the rest of the buffer, up to `lim`.
  have hC₃ : Common s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (hne r hr)) m₃ rd₃ wr₃
  refine WP.seq (wp_mov32i fun s₄ u₄ _ _ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hrax₅ : s₅.gpr .rax = BitVec.ofNat 64 (56 + 8 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.other _ (by decide), hrax₃, g₃ _ (by decide), h.r13,
      sub_ofNat (by omega)]
  have hZ : Zero s₀ s n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .rax ∧ r ≠ .r9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r13, Nat.add_zero]
    · rw [hrax₅, Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  have hz₅ : s₅.zf = some (decide (56 + 8 * k - n = 0)) := by
    rw [z₅, ← u₅.gpr, hrax₅, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (56 + 8 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.rbx],
      by rw [hZ₆.keep _ (by simp), hC.r15], by rw [hZ₆.keep _ (by simp), hC.rbp],
      by rw [hZ₆.keep _ (by simp), hC.r12], by rw [hZ₆.keep _ (by simp), hC.rsp],
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
  have h14₆ : s₆.gpr .r14 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.r14]
  -- In the last block, the length.
  refine WP.seq (wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_)
  have hC₇ : Common s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [g₇]) m₇ rd₇ wr₇
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, h14₆, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .r14 = BitVec.ofNat 64 k ∧
      stateAt s₈.mem (st s₀) = stateAt s.mem (st s₀) ∧
      ∀ m, R₀ s₀ m → bytesAt s₈.mem (st s₀ + 32) 64 = bytesAt s.mem (st s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)) ?_
    fun s₈ ⟨hC₈, h14₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hout : InRegions s₇.wr (st s₀ + BitVec.ofInt 64 ((88 : Nat) : Int)) 8 :=
        ⟨stR s₀, by simp [hC₇.wr, hp.wr], contains_offset' (by omega) (by omega)⟩
      refine wp_mov fun s₈ u₈ _ _ => wp_add fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => wp_add fun s₁₁ u₁₁ =>
        wp_bswap fun s₁₂ u₁₂ => wp_store (a := st s₀ + BitVec.ofInt 64 ((88 : Nat) : Int)) ?_ ?_
        fun s₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ => WP.block_nil ?_
      · simp only [State.ea, at_, u₁₂.other .rbx (by decide), u₁₁.other .rbx (by decide),
          u₁₀.other .rbx (by decide), u₉.other .rbx (by decide), u₈.other .rbx (by decide), hC₇.rbx]
      · rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr]; exact hout
      have keep : ∀ r, r ≠ .rax → s₁₃.gpr r = s₇.gpr r := fun r h => by
        rw [g₁₃, u₁₂.other r h, u₁₁.other r h, u₁₀.other r h, u₉.other r h, u₈.other r h]
      have hv : s₁₂.gpr .rax = bswap64 (BitVec.ofNat 64 (8 * (s₀.gpr .rsi).toNat)) := by
        rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.gpr, hC₇.r12, times8]
      have hm₁₂ : s₁₂.mem = s₇.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
      let L := (List.range 8).map fun j =>
        (bswap64 (BitVec.ofNat 64 (8 * (s₀.gpr .rsi).toNat))).extractLsb' (8 * j) 8
      have hw : s₁₃.mem = writeBytes s₆.mem (st s₀ + 32 + BitVec.ofNat 64 56) L := by
        rw [m₁₃, hm₁₂, m₇, hv, show st s₀ + 32 + BitVec.ofNat 64 56 = st s₀ + BitVec.ofInt 64 ((88 : Nat) : Int) by
          rw [ofInt_natCast, BitVec.add_assoc]; rfl, Mem.writeW,
          write_eq_writeBytes]
        rfl
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := 56) (xs := L) (by simp [L])
      refine ⟨⟨rd₁₃.trans (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd]; exact hC₇.rd),
        wr₁₃.trans (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr]; exact hC₇.wr),
        by rw [keep _ (by decide), hC₇.rbx], by rw [keep _ (by decide), hC₇.r15],
        by rw [keep _ (by decide), hC₇.rbp], by rw [keep _ (by decide), hC₇.r12],
        by rw [keep _ (by decide), hC₇.rsp], by rw [hw]; exact hfr, by rw [hw]; exact hsv⟩,
        by rw [keep _ (by decide), g₇, h14₆], ?_, fun m hm => ?_⟩
      · rw [hw, ← hst₆]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [L])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₆.mem (st s₀ + 32) 56 L (by simp [L])
        simp only [L, List.length_map, List.length_range] at e
        rw [hw, e, bswap64_bytes, len_bits hm.2, hby₆]
        simp [lenBytes, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, by rw [g₇, h14₆], by rw [m₇, hst₆], fun m _ => ?_⟩
      rw [m₇, hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_mov fun s₉ u₉ _ _ => wp_addi fun s₁₀ u₁₀ => WP.block_nil ?_)
  have hC₁₀ : Common s₀ s₁₀ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .rsi := by simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [u₁₀.other r this, u₉.other r this]) (by rw [u₁₀.mem, u₉.mem]) (by rw [u₁₀.rd, u₉.rd])
    (by rw [u₁₀.wr, u₉.wr])
  have hrsi : s₁₀.gpr .rsi = st s₀ + 32 := by
    rw [u₁₀.gpr, u₉.gpr, hC₈.rbx]; rfl
  refine WP.seq (compress_buf hp hC₁₀ hrsi fun s₁₁ hC₁₁ cs₁₁ hst₁₁ hdi₁₁ hcx₁₁ => ?_)
  have h14₁₁ : s₁₁.gpr .r14 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h14₈]
  have hblk : ∀ m, R₀ s₀ m → blockAt s₁₀.mem (st s₀ + 32) = parseBlock fun t =>
      (bytesAt s.mem (st s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0 := by
    intro m hm
    apply parseBlock_congr
    intro t ht
    rw [u₁₀.mem, u₉.mem]
    exact bytesAt_getD (hby₈ m hm) ht
  -- Next block, if any.
  refine wp_mov32i fun s₁₂ u₁₂ _ _ => wp_subi fun s₁₃ u₁₃ z₁₃ => WP.block_nil ?_
  have hC₁₃ : Common s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .r14 ∧ r ≠ .r13 := by simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr])
  have hz : s₁₃.zf = some (decide (k = 1)) := by
    rw [z₁₃, u₁₂.other _ (by decide), h14₁₁, show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from
      rfl, sub_beq (by omega) (by omega)]
  have hst : ∀ m, R₀ s₀ m → stateAt s₁₃.mem (st s₀) = compress (stateAt s.mem (st s₀)) (parseBlock fun t =>
      (bytesAt s.mem (st s₀ + 32) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro m hm
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₁₀.mem, u₉.mem, hst₈, ← hblk m hm, u₁₀.mem, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by simp [eval, hz], rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun m hm => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h14₁₁]; rfl
    · rw [h.hash m hm]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst m hm]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by simp [eval, hz], ⟨hC₁₃, fun m hm => ?_⟩,
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), hdi₁₁],
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), hcx₁₁]⟩
    rw [h.hash m hm, hst m hm]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The memory after saving the callee-saved registers. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((112 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((120 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((136 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((144 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((152 : Nat) : Int)) (s₀.gpr .r15)

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  intro p hp
  simp only [Impl.Sha256.X86_64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [saveMem, Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame {s₀ : State} : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 160 →
      (scR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 120 (by omega))).writeW (List.mem_singleton_self _) _
    (c 128 (by omega))).writeW (List.mem_singleton_self _) _ (c 136 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 144 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 152 (by omega))

theorem R₀.length {s₀ : State} {m : List Byte} (h : R₀ s₀ m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem prologue_eq : save .rcx ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rsi), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 63),
      .mov32 .rax (.imm 0x80), .store8 bufByte .rax, .alu .add .r13 (.imm 1),
      .mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 57)] = [
    .store (at_ .rcx 112) .rbx, .store (at_ .rcx 120) .rbp, .store (at_ .rcx 128) .r12,
    .store (at_ .rcx 136) .r13, .store (at_ .rcx 144) .r14, .store (at_ .rcx 152) .r15,
    .mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
    .mov .r12 (.reg .rsi), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 63),
    .mov32 .rax (.imm 0x80), .store8 bufByte .rax, .alu .add .r13 (.imm 1),
    .mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 57)] := rfl

set_option maxHeartbeats 1000000 in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.seq (.block (save .rcx ++ [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx), .mov .rbp (.reg .rdx),
      .mov .r12 (.reg .rsi), .mov .r13 (.reg .rsi), .alu .and .r13 (.imm 63),
      .mov32 .rax (.imm 0x80), .store8 bufByte .rax, .alu .add .r13 (.imm 1),
      .mov32 .r14 (.imm 0), .alu .cmp .r13 (.imm 57)]))
      (.ite .ae (.block [.mov32 .r14 (.imm 1)]) (.block []))) s₀
      fun s => ∃ k, LInv s₀ k (cnt s₀ % 64 + 1) s := by
  have o : ∀ d : Nat, d + 8 ≤ 160 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR s₀, by simp [hp.wr], contains_offset' hd (by omega)⟩
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [prologue_eq]
  refine WP.seq (wp_store (a := scr s₀ + BitVec.ofInt 64 ((112 : Nat) : Int)) rfl (o 112 (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_)
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((120 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o 120 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) (by simp only [State.ea, at_, g₂, g₁])
    (by rw [wr₂, wr₁]; exact o 128 (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((136 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o 136 (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((144 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o 144 (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((152 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o 152 (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have hg₆ : s₆.gpr = s₀.gpr := by rw [g₆, g₅, g₄, g₃, g₂, g₁]
  have hm₆ : s₆.mem = saveMem s₀ := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [saveMem, g₅, g₄, g₃, g₂, g₁]
  refine wp_mov fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ =>
    wp_mov fun s₁₁ u₁₁ _ _ => wp_andi fun s₁₂ u₁₂ => ?_
  have hC₁₂ : Common s₀ s₁₂ := by
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
      exact saveMem_frame.mono (by simp)
    · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]; exact saveMem_saved
  have hm₁₂ : s₁₂.mem = saveMem s₀ := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  have hr13 : s₁₂.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % 64) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), hg₆]
    exact and63 _
  -- The `0x80` byte.
  have hout : InRegions s₁₂.wr (st s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) 1 := by
    refine ⟨stR s₀, by simp [hC₁₂.wr, hp.wr], ?_⟩
    rw [st_add]; exact contains_offset (by omega) (by omega)
  refine wp_mov32i fun s₁₃ u₁₃ _ _ => wp_store8 (a := st s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) ?_
    (by rw [u₁₃.wr]; exact hout) fun s₁₄ g₁₄ m₁₄ rd₁₄ wr₁₄ => ?_
  · simp only [State.ea, bufByte, u₁₃.other .rbx (by decide), u₁₃.other .r13 (by decide), hC₁₂.rbx, hr13,
      BitVec.mul_one, show BitVec.ofInt 64 32 = 32 from rfl]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₁₂.writeBuf hp (n := cnt s₀ % 64) (xs := [0x80]) (by simp; omega)
  have hm₁₄ : s₁₄.mem = writeBytes s₁₂.mem (st s₀ + 32 + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [m₁₄, u₁₃.mem, u₁₃.gpr, ← List.nil_append [(0x80 : Byte)], writeBytes_snoc _ _ _ _ (by simp),
      writeBytes_nil]
    simp
  refine wp_addi fun s₁₅ u₁₅ => wp_mov32i fun s₁₆ u₁₆ _ _ => wp_cmpi fun s₁₇ g₁₇ m₁₇ rd₁₇ wr₁₇ cf₁₇ _ =>
    WP.block_nil ?_
  have keep : ∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .rax → s₁₇.gpr r = s₁₂.gpr r := fun r h1 h2 h3 => by
    rw [g₁₇, u₁₆.other r h2, u₁₅.other r h1, g₁₄, u₁₃.other r h3]
  have hm₁₇ : s₁₇.mem = s₁₄.mem := by rw [m₁₇, u₁₆.mem, u₁₅.mem]
  have hC₁₇ : Common s₀ s₁₇ :=
    ⟨by rw [rd₁₇, u₁₆.rd, u₁₅.rd, rd₁₄, u₁₃.rd, hC₁₂.rd], by rw [wr₁₇, u₁₆.wr, u₁₅.wr, wr₁₄, u₁₃.wr, hC₁₂.wr],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rbx],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.r12],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rsp],
      by rw [hm₁₇, hm₁₄]; exact hfr, by rw [hm₁₇, hm₁₄]; exact hsv⟩
  have hr13' : s₁₇.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % 64 + 1) := by
    rw [g₁₇, u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, u₁₃.other _ (by decide), hr13, ofNat_succ]; rfl
  have hcf : s₁₇.cf = some (decide (cnt s₀ % 64 + 1 < 57)) := by
    rw [cf₁₇, u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, u₁₃.other _ (by decide), hr13,
      show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, ← ofNat_succ,
      show BitVec.signExtend 64 (57 : BitVec 32) = BitVec.ofNat 64 57 by decide,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := cnt s₀ % 64 + 1) (by omega),
      Nat.mod_eq_of_lt (a := 57) (by norm_num)]
  -- The facts about the buffer.
  have hbytes : ∀ m, R₀ s₀ m → bytesAt s₁₇.mem (st s₀ + 32) (cnt s₀ % 64 + 1) =
      rest m ++ [0x80] := by
    intro m hm
    have e := bytesAt_writeBytes s₁₂.mem (st s₀ + 32) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₇, hm₁₄, e, hm₁₂]
    congr 1
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := saveMem_frame.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) (i := 32 + i)
      (by show 32 + i < 96; omega)
    rwa [← st_add] at this
  have hstate : stateAt s₁₇.mem (st s₀) = stateAt s₀.mem (st s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₇, hm₁₄, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₁₂]
    exact saveMem_frame.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) (by show i < 96; omega)
  refine WP.ite (!decide (cnt s₀ % 64 + 1 < 57)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hb
    refine wp_mov32i fun s₁₈ u₁₈ _ _ => WP.block_nil ⟨1, hC₁₇.of_gpr (fun r hr => u₁₈.other r (by
      simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide)) u₁₈.mem u₁₈.rd u₁₈.wr,
      le_rfl, by omega, by rw [u₁₈.other _ (by decide), hr13'], by rw [u₁₈.gpr]; rfl, fun m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, u₁₈.mem, hbytes m hm, hstate, hm.1.1,
      ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 63 - cnt s₀ % 64 by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.block_nil ⟨0, hC₁₇, by omega, by omega, hr13', ?_, fun m hm => ?_⟩
    · rw [g₁₇, u₁₆.gpr]; rfl
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes m hm, hstate, hm.1.1,
      ← hm.length, show 56 - (cnt s₀ % 64 + 1) = 55 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

/-- Word `k` of the digest. -/
def outW (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rbx (4 * k))), .bswap32 .rax, .store32 (at_ .rbp (4 * k)) .rax]

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ [Reg.rbx, .rbp, .r15, .rsp], s.gpr r = sD.gpr r
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

set_option maxHeartbeats 1000000 in
theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : Out s₀ sD 8 s) :
    WP isa (.block restore) s fun s' =>
      abiPreserved s₀ s' ∧ Spec.Sha256.finalizeX86_64.post s₀ s' := by
  have hC := hD.1
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes)
    (by rw [flat_length _ _ le_rfl])
  have i : ∀ d : Nat, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset' hd (by omega)⟩
  have sv : ∀ r d, (r, d) ∈ saved → s.mem.readW (scr s₀ + BitVec.ofInt 64 ((d : Nat) : Int)) 64 = s₀.gpr r := by
    intro r d hrd
    rw [h.mem, ← hC.saved _ hrd]
    have hd : 112 ≤ d ∧ d + 8 ≤ 160 := by
      simp only [Impl.Sha256.X86_64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      rcases hrd with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (d : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact (hp.out_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)))
  have i0 := i 112 (by omega); have i1 := i 120 (by omega); have i2 := i 128 (by omega)
  have i3 := i 136 (by omega); have i4 := i 144 (by omega); have i5 := i 152 (by omega)
  have g0 := sv .rbx 112 (by simp [saved]); have g1 := sv .rbp 120 (by simp [saved])
  have g2 := sv .r12 128 (by simp [saved]); have g3 := sv .r13 136 (by simp [saved])
  have g4 := sv .r14 144 (by simp [saved]); have g5 := sv .r15 152 (by simp [saved])
  have hr15 : s.gpr .r15 = scr s₀ := by rw [h.keep _ (by simp), hC.r15]
  have hrsp : s.gpr .rsp = s₀.gpr .rsp := by rw [h.keep _ (by simp), hC.rsp]
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
    rw [h.mem, hfo.readW (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    exact hC.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  apply WP.of_runBlock
  rw [Update.restore_eq]
  simp (config := {decide := true}) only [runBlock_cons (M := isa), runStep_some (M := isa),
    runBlock_nil (M := isa), exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · have e := bytesAt_writeBytes sD.mem (out s₀) 0 (((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes)
      (by rw [flat_length _ _ le_rfl]; omega)
    have e' : bytesAt (writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes))
        (out s₀) 32 = ((stateAt sD.mem (st s₀)).toList.take 8).flatMap wordBytes := by
      rw [flat_length _ _ le_rfl, show out s₀ + BitVec.ofNat 64 0 = out s₀ by simp,
        show bytesAt sD.mem (out s₀) 0 = [] from rfl, List.nil_append] at e
      exact e
    rw [← h.mem] at e'
    rw [e', hD.2 m ⟨hm, hc⟩, List.take_of_length_le (by simp)]

theorem writeW_bswap32 (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (bswap32 w) = writeBytes m a (wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bswap32_bytes']; rfl

set_option maxHeartbeats 1000000 in
theorem out_step {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) {k : Nat} (hk : k < 8)
    {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hrbx : s.gpr .rbx = st s₀ := by rw [h.keep _ (by simp), hC.rbx]
  have hrbp : s.gpr .rbp = out s₀ := by rw [h.keep _ (by simp), hC.rbp]
  have hP := flat_length (stateAt sD.mem (st s₀)) k hk.le
  refine wp_mov32m (a := st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (by simp [State.ea, at_, hrbx])
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset' (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_bswap32 fun s₂ u₂ => wp_store32 (a := out s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int))
    (by simp [State.ea, at_, u₂.other .rbp (by decide), u₁.other .rbp (by decide), hrbp])
    (by rw [u₂.wr, u₁.wr]; exact ⟨outR s₀, by simp [h.wr, hp.wr], contains_offset' (by omega) (by omega)⟩)
    fun s₃ g₃ m₃ rd₃ wr₃ => hnext s₃ ⟨by rw [rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₃, u₂.wr, u₁.wr, h.wr],
      fun r hr => ?_, ?_⟩
  · have : r ≠ .rax := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
    rw [g₃, u₂.other r this, u₁.other r this, h.keep r hr]
  · have hread : s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 =
        (stateAt sD.mem (st s₀))[k] := by
      rw [h.mem, (out_frame s₀ sD.mem _ (by omega)).readW
        (r := ⟨st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · rw [ofInt_natCast]; simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hp.st_out.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega) (by omega))
    rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hread, BitVec.setWidth_setWidth_of_le _ (by omega),
      BitVec.setWidth_eq, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, h.mem,
      writeW_bswap32, ofInt_natCast, ← hP]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem out_all {s₀ : State} (hp : Pre s₀) {sD : State} (hD : Done s₀ sD) :
    ∀ j ≤ 8, ∀ s, Out s₀ sD (8 - j) s →
      WP isa (.block (((List.range 8).drop (8 - j)).flatMap outW ++ restore)) s fun s' =>
        abiPreserved s₀ s' ∧ Spec.Sha256.finalizeX86_64.post s₀ s' := by
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

theorem WP.seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

theorem out_keeps : (((List.range 8).flatMap outW ++ restore).all fun i =>
    Taint.dstOf i != some .rdi && Taint.dstOf i != some .rcx) = true := by decide +kernel

/-- `finalize` is correct, and leaves `rdi` and `rcx` as they were (which code
inlining it relies on). -/
theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.finalizeX86_64.post s₀ s' ∧
      s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  unfold finalize
  rw [← WP.seq_assoc]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => Done s₀ s ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rcx = scr s₀) ?_
    fun sD ⟨hD, hdi, hcx⟩ => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have := out_all hp hD 8 le_rfl sD ⟨hD.1.rd, hD.1.wr, fun _ _ => rfl, by simp [writeBytes_nil]⟩
    rw [show 8 - 8 = 0 from rfl, List.drop_zero] at this
    have keeps := fun i hi => List.all_eq_true.mp out_keeps i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at keeps
    refine WP.mono (WP.gpr (WP.gpr this (r := .rdi) fun i hi => (keeps i hi).1) (r := .rcx)
      fun i hi => (keeps i hi).2) fun s' ⟨⟨h, h₁⟩, h₂⟩ => ⟨h.1, h.2, ?_, ?_⟩
    · rw [h₁, hdi]
    · rw [h₂, hcx]

/-- The initial taint: the arguments are public, and `rdi`, `rdx` and `rcx`
point at the writable regions. -/
def τ₀ : X86_64.Taint.T :=
  { regs := [.rdi, .rsi, .rdx, .rcx], flags := false, lens := [96, 32, 160],
    bases := [(.rdi, 0), (.rdx, 1), (.rcx, 2)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Spec.Sha256.finalizeX86_64.pre s₁)
    (h₂ : Spec.Sha256.finalizeX86_64.pre s₂) (hpub : Spec.Sha256.finalizeX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  have wf : ∀ s, Spec.Sha256.finalizeX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d1, d2, d3, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d1, d2, d3], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_⟩
  · simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p3, p4]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 160⟩]

theorem finalize_verified : Verified X86_64.target finalize Spec.Sha256.finalizeX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h.1, h.2.1⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha256.X86_64.Stream.Finalize
