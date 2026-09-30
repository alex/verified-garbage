import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, sampling

Untrusted: everything here is checked by Lean. `parse k` runs 168
iterations of `vg_mlkem_sample_ntt`'s loop on the 504 bytes of XOF output
of seed `k` (`loop_ok`, as `SampleNtt.lean`'s), to polynomial `k`; and, if
they sample fewer than 256 coefficients, calls `vg_mlkem_sample_ntt` on the
seed (`fallback_ok`). Either way, polynomial `k` is then the seed's
`SampleNTT`, if it succeeds, and `r14` records whether the first `k + 1` do
(`parse_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter)
open VG.Spec.Sha3 (bytesAt)

/-- Whether the first `K` seeds sample their polynomials. -/
def okN (σ : State) (K : Nat) : Nat :=
  if (List.range K).all fun k => (sampleNTT minIterations (B σ k)).isSome then 1 else 0

/-- Before `parse K`. -/
structure PInv (σ : State) (K : Nat) (s : State) : Prop where
  env : Env σ s
  buf : ∀ k < 4, ∀ p < 504, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) p
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ K)
  polys : ∀ k < K, ∀ f, sampleNTT minIterations (B σ k) = some f → PolyIs s.mem (poly4 (aP σ) k) f

/-- The coefficients of seed `K` after `t` iterations. -/
abbrev Lt (σ : State) (K t : Nat) : List Zq := sampleAfter [] (xofByte (B σ K)) t

/-- At the start of iteration `t` of `parse K`. -/
structure LAt (σ : State) (K t : Nat) (s : State) : Prop where
  pinv : PInv σ K s
  rsi : s.gpr .rsi = at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ K t).length
  rbp : s.gpr .rbp = poly4 (aP σ) K
  stored : Stored s.mem (poly4 (aP σ) K) (Lt σ K t)

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem sub_poly {K : Nat} (hK : K < 4) : Region.Sub (pR (poly4 (aP σ) K)) (aR σ) := Offset.sub_base _ (by omega)

/-- Writes to polynomial `K` keep `PInv` but for polynomial `K`, and the registers. -/
theorem PInv.poly {K : Nat} (hK : K < 4) {s s' : State} (h : PInv σ K s)
    (hf : Frame [pR (poly4 (aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14] → s'.gpr r = s.gpr r) : PInv σ K s' := by
  have hsub := sub_poly (σ := σ) hK
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub fun r hr => ?_)⟩,
    fun k hk p hp' => ?_, by rw [hg .r14 (by simp), h.r14], fun k hk f e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using (hp.a_scr.symm.sub_left (sub_scr (by simp only [oSave]; omega))).sub_right hsub) (by decide)]
    exact h.env.saved i hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨aR σ, by simp, hsub⟩
  · rw [buf_frame (by simpa using (hp.a_scr.symm.sub_left (sub_scr (by simp only [oBuf]; omega))).sub_right hsub)
      hf hk hp']
    exact h.buf k hk p hp'
  · have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
      (by omega)
    exact polyIs_frame hf (by simpa [poly4] using hd) (h.polys k hk f e)

omit hp in
theorem out_byte {K t : Nat} (hK : K < 4) {s : State} (h : LAt σ K t s) {j : Nat} (hj : 3 * t + j < 504) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = xofByte (B σ K) (3 * t + j) := by
  have e := h.pinv.buf K hK (3 * t + j) hj
  rw [at'] at e
  rw [h.rsi, at', Offset.add_add, Offset.add_add]
  exact e

theorem lat_regions {K t : Nat} (hK : K < 4) {s : State} (h : LAt σ K t s) {j : Nat} (hj : 3 * t + j < 504) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [h.rsi, at', Offset.add_add, Offset.add_add]
  exact in_scr' hp h.pinv.env.rd h.pinv.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem lat_step {K t : Nat} (hK : K < 4) (ht : t < 168) {s : State} (h : LAt σ K t s) :
    WP isa snBody s fun s' => LAt σ K (t + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hL : (Lt σ K t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  have hw : WrA s.wr (poly4 (aP σ) K) := fun j hj => by
    rw [h.pinv.env.wr, hp.wr]
    refine ⟨aR σ, by simp, ?_⟩
    rw [coeffAddr, poly4, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (snBody_ok s (aP := poly4 (aP σ) K) h.rbp h.rdi hL hw h.stored
    (by simpa using lat_regions hp hK h (j := 0) (by omega)) (lat_regions hp hK h (by omega))
    (lat_regions hp hK h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := out_byte hK h (j := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  rw [e0, out_byte hK h (j := 1) (by omega), out_byte hK h (j := 2) (by omega), ← sampleAfter_succ] at hdi hst
  refine ⟨⟨h.pinv.poly hp hK hf hk.2.1 hk.2.2 fun r hr => hk.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, h.rsi, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, Offset.add_add, Nat.mul_succ], hdi,
    by rw [hk.gpr (by decide), h.rbp], hst⟩, hcx, hz⟩

omit hp in
/-- `PInv` after code that writes no memory and keeps its registers. -/
theorem PInv.keep {K : Nat} {s s' : State} (h : PInv σ K s) (hm : s'.mem = s.mem) {rs : List Reg}
    (hk : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs) : PInv σ K s' :=
  ⟨h.env.keep hm hk fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hm]; exact h.buf, by rw [hk.gpr (hrs .r14 (by simp)), h.r14],
    by rw [hm]; exact h.polys⟩

omit hp in
theorem setup_eq (K : Nat) : ([.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
    .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
    .mov32 .rcx (.imm 168)] : List Instr) = [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
    .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
    .mov32 .rcx (.imm 168)] := rfl

/-- The setup and the 168 iterations. -/
theorem loop_ok {K : Nat} (hK : K < 4) {s : State} (h : PInv σ K s) {rest : Prog isa} {Q : State → Prop}
    (kont : ∀ s', LAt σ K 168 s' → WP isa rest s' Q) :
    WP isa (.seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
      .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
      .mov32 .rcx (.imm 168)]) (.seq (.loop snBody .ne) rest)) s Q := by
  refine WP.seq (WP.mono (WP.keep [.rsi, .rdi, .rbp, .rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ (oBuf + 504 * K) ∧ s'.gpr .rdi = 0 ∧ s'.gpr .rbp = poly4 (aP σ) K ∧
      s'.gpr .rcx = BitVec.ofNat 64 168)
    (by xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 504 * K < 2 ^ 31 by simp only [oBuf]; omega),
      sx_ofNat (show 1024 * K < 2 ^ 31 by omega)]; rfl) rfl) fun s₁ ⟨⟨hm, hsi, hdi, hbp, hcx⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .rcx) (N := 168) (by decide) (by decide) (fun t s => LAt σ K t s)
    (fun t ht s hs _ => lat_step hp hK ht hs) (fun _ h => h) ?_ hcx) kont)
  exact ⟨h.keep hm k₁ (by decide), by rw [hsi, Nat.mul_zero, add_ofNat_zero], by rw [hdi]; rfl, hbp,
    fun k hk => absurd hk (by simp [sampleAfter])⟩

/-! ## The fallback -/

omit hp in
theorem okN_succ (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (okN σ K)).setWidth 32 &&&
    (if (sampleNTT minIterations (B σ K)).isSome then 1 else 0)) = BitVec.ofNat 64 (okN σ (K + 1)) := by
  simp only [okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range K).all fun k => (sampleNTT minIterations (B σ k)).isSome <;>
    cases (sampleNTT minIterations (B σ K)).isSome <;> rfl

/-- The seed at `seeds + 34 K`. -/
theorem seed_bytes {K : Nat} (hK : K < 4) {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) :
    bytesAt m (sd σ + BitVec.ofNat 64 (34 * K)) 34 = B σ K := by
  rw [bytesAt_frame hf (by simpa using ⟨hp.sd_a.sub_left (Offset.sub_base _ (by omega)),
    hp.sd_scr.sub_left (Offset.sub_base _ (by omega)), (hp.stk_sd.sub_right (Offset.sub_base _ (by omega))).symm⟩)
    (by decide)]
  rfl

theorem scr6144_lt : (at' σ oScalar).toNat + 2048 ≤ 2 ^ 64 := by
  have := hp.scr_lt
  rw [at', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show oScalar < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (by simp only [oScalar]; omega)]
  simp only [oScalar]; omega

/-- The regions of `vg_mlkem_sample_ntt`'s call for seed `K`. -/
abbrev cRd (σ : State) (K : Nat) : List Region := [⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩]
abbrev cWr (σ : State) (K : Nat) : List Region := [pR (poly4 (aP σ) K), ⟨at' σ oScalar, 2048⟩]

omit hp in
theorem c_sub {K : Nat} (hK : K < 4) : ∀ r ∈ cWr σ K ++ [stkR σ],
    (∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨aR σ, by simp, sub_poly hK⟩
  · exact ⟨scrR σ, by simp, sub_scr (by simp only [oScalar]; omega)⟩
  · exact ⟨stkR σ, by simp, fun _ h => h⟩

/-- A region the call writes is apart from `⟨at' σ a, n⟩` in the scratch space below 6144. -/
theorem c_disj {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ cWr σ K ++ [stkR σ], Region.Disjoint ⟨at' σ a, n⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact (hp.a_scr.symm.sub_left (sub_scr (by simp only [oScalar] at h; omega))).sub_right (sub_poly hK)
  · exact Offset.disjoint _ (.inl h) (by simp only [oScalar] at h; omega) (by simp only [oScalar]; omega)
  · exact (hp.stk_scr.sub_right (sub_scr (by simp only [oScalar] at h; omega))).symm

/-- `PInv` after the call. -/
theorem PInv.call {K : Nat} (hK : K < 4) {s s' : State} (h : PInv σ K s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r)
    (hf : Frame (cWr σ K ++ [stkR σ]) s.mem s'.mem) : PInv σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub (c_sub (σ := σ) hK))⟩,
    fun k hk p hp' => ?_, by rw [hg .r14 (by simp), h.r14], fun k hk f e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (c_disj hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · rw [buf_frame (c_disj hp hK (by simp only [oBuf, oScalar]; omega)) hf hk hp']
    exact h.buf k hk p hp'
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk f e)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
        (by omega)
      simpa [poly4] using hd
    · exact (hp.a_scr.sub_left (sub_poly (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega))
    · exact (hp.stk_a.sub_right (sub_poly (by omega))).symm

omit hp in
theorem sx6144 : BitVec.signExtend 64 (BitVec.ofNat 32 oScalar) = BitVec.ofNat 64 6144 := by decide

theorem regs {s : State} (he : Env σ s) : s.rd ++ s.wr = [sdR σ, aR σ, scrR σ] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov {s : State} (he : Env σ s) {K : Nat} (hK : K < 4) :
    Covers (cRd σ K ++ cWr σ K) (s.rd ++ s.wr) ∧ Covers (cWr σ K) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rw [regs hp he]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sdR σ, by simp, 34 * K, rfl, by simp only; omega⟩
    · exact ⟨aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩
  · rw [he.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩

omit hp in
theorem sx34 {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (34 * K)) = BitVec.ofNat 64 (34 * K) :=
  sx_ofNat (by omega)

omit hp in
theorem sx1024 {K : Nat} (hK : K < 4) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (1024 * K)) = BitVec.ofNat 64 (1024 * K) := sx_ofNat (by omega)

omit hp in
theorem and14_ok (s : State) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s fun s' =>
      (s'.gpr .r14 = BitVec.setWidth 64 ((s.gpr .r14).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r14] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- The call of `vg_mlkem_sample_ntt` on seed `K`. -/
theorem call_ok {K : Nat} (hK : K < 4) {s : State} (h : PInv σ K s) :
    WP isa (.seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
          .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
          .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
        (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r14 (.reg .rax)]))) s
      (PInv σ (K + 1)) := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .rdx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = sd σ + BitVec.ofNat 64 (34 * K) ∧ s'.gpr .rsi = poly4 (aP σ) K ∧ s'.gpr .rdx = at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.rbx, sx34 hK, sx1024 hK, sx6144]; exact ⟨rfl, rfl⟩) rfl)
    fun s₂ ⟨⟨hm₂, hdi, hsi, hdx⟩, k₂⟩ => ?_)
  have h₂ : PInv σ K s₂ := h.keep hm₂ k₂ (by decide)
  have hsp : s₂.gpr .rsp = σ.gpr .rsp := h₂.env.rsp
  have kS : (below (s₂.gpr .rsp) 24).Disjoint ⟨sd σ + BitVec.ofNat 64 (34 * K), 34⟩ := by
    rw [hsp]; exact hp.stk_sd.sub_right (Offset.sub_base (sd σ) (d := 34 * K) (n := 34) (by omega))
  have kA : (below (s₂.gpr .rsp) 24).Disjoint (pR (poly4 (aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (sub_poly (σ := σ) hK)
  have kZ : (below (s₂.gpr .rsp) 24).Disjoint ⟨at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  have hpre : sampleK.pre (s₂.callEntry.withRegions (cRd σ K) (cWr σ K)) := by
    simp only [sampleK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      ce_gpr' s₂ (by decide : Reg.rdi ≠ .rsp), ce_gpr' s₂ (by decide : Reg.rsi ≠ .rsp),
      ce_gpr' s₂ (by decide : Reg.rdx ≠ .rsp), hdi, hsi, hdx]
    exact ⟨trivial, trivial,
      (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_poly hK),
      (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (sub_scr (by simp only [oScalar]; omega)),
      (hp.a_scr.sub_left (sub_poly hK)).sub_right (sub_scr (by simp only [oScalar]; omega)),
      ret_disj s₂ kS, ret_disj s₂ kA, ret_disj s₂ kZ, stk_disj s₂ kS, stk_disj s₂ kA, stk_disj s₂ kZ,
      scr6144_lt hp⟩
  have hcv := cov hp h₂.env hK
  refine WP.seq (WP.call sample_correct sample_nosp (by rw [sample_depth]; decide) hpre hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, hg₃, hpost⟩ => ?_)
  rw [sample_depth, hsp] at hf
  have h₃ : PInv σ K s₃ := h₂.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf
  simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s₂ (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s₂ (by decide : Reg.rsi ≠ .rsp), hdi, hsi, hm₃, ce_bytesAt s₂ (n := 34) (by decide) kS, hm₂,
    seed_bytes hp hK h.env.frame] at hpost
  rw [hg₃ .rax (by decide)] at hpost
  refine WP.mono (and14_ok s₃) fun s₄ ⟨⟨h14, hm₄⟩, k₄⟩ => ?_
  refine ⟨⟨k₄.2.1.trans h₃.env.rd, k₄.2.2.trans h₃.env.wr, by rw [k₄.gpr (by decide), h₃.env.rbx],
      by rw [k₄.gpr (by decide), h₃.env.r12], by rw [k₄.gpr (by decide), h₃.env.r13],
      by rw [k₄.gpr (by decide), h₃.env.rsp], by rw [k₄.gpr (by decide), h₃.env.r15],
      by rw [hm₄]; exact h₃.env.saved, by rw [hm₄]; exact h₃.env.frame⟩,
    by rw [hm₄]; exact h₃.buf, by rw [h14, h₃.r14, hpost.1, okN_succ], fun k hk f e => ?_⟩
  rw [hm₄]
  by_cases ek : k = K
  · subst ek; exact hpost.2 f e
  · exact h₃.polys k (by omega) f e

/-- The check of `j`, and the call if it is less than 256. -/
theorem fallback_ok {K : Nat} (hK : K < 4) {s : State} (h : LAt σ K 168 s) :
    WP isa (fallback K) s (PInv σ (K + 1)) := by
  unfold fallback
  refine WP.seq (WP.mono (cmpRdi_ok s) fun s₁ ⟨hc, hm, hg, hrd, hwr⟩ => ?_)
  have hL : (Lt σ K 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  rw [h.rdi, ofNat64_toNat (by omega)] at hc
  have h₁ : PInv σ K s₁ := h.pinv.keep hm (rs := []) ⟨fun r _ => by rw [hg], hrd, hwr⟩ (by simp)
  refine WP.ite _ hc (fun _ => call_ok hp hK h₁) fun hb => WP.block_nil ?_
  have hfull : (Lt σ K 168).length = 256 := by
    rw [decide_eq_false_iff_not] at hb; omega
  have hs : sampleNTT minIterations (B σ K) = some (toPoly (Lt σ K 168)) :=
    sampleNTT_of_full (by decide) (by rw [n_eq]; exact hfull)
  refine ⟨h₁.env, h₁.buf, ?_, fun k hk f e => ?_⟩
  · have e : okN σ (K + 1) = okN σ K := by
      simp only [okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true, hs,
        Option.isSome_some]
    rw [h₁.r14, e]
  · by_cases ek : k = K
    · subst ek
      rw [hs] at e
      rw [← Option.some.inj e]
      exact SampleNtt.stored_polyAt (by rw [hm]; exact h.stored) hfull
    · exact h₁.polys k (by omega) f e

/-- `parse K`. -/
theorem parse_ok {K : Nat} (hK : K < 4) {s : State} (h : PInv σ K s) : WP isa (parse K) s (PInv σ (K + 1)) := by
  unfold parse
  exact loop_ok hp hK h fun _ h' => fallback_ok hp hK h'

end

end VG.Proof.MlKem.X86_64.S4
