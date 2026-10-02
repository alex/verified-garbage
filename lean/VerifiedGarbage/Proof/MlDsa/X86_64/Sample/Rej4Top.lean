import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Parse
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, correctness

The pieces, in order: the prologue, the round constants and the padded seeds,
and three squeezes (as in `vg_mlkem_sample_ntt4_avx2`); the counts zeroed; the
first half of each seed (`P1`); three more squeezes; the second half of each
seed, which leaves the coefficients of its 1008 bytes of output and the AND of
whether each has 256 in `r14` (`P2`); and the epilogue, which returns it
(`r4K`, as `vg_mldsa_rej_ntt_poly`'s contract `rnK` for each seed).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (Keep ea_at add_ofNat_zero pR WP.keep ofNat64_pred sample4K)
open VG.Proof.MlKem.X86_64.S4
open VG.Proof.MlDsa.Sample (rnFold Stored stored_nil stored_frame stored_polyIs toPoly G_length)
open VG.Spec.MlKem (poly4 seed4)
open VG.Spec.MlDsa (Zq G PolyIs)
open VG.Proof.MlKem (xofByte)

/-- `vg_mldsa_rej_ntt_poly4(seeds = rdi, a = rsi, scratch = rdx) -> eax`
(either implementation), with 24 bytes of stack below `rsp`: for each seed,
what `vg_mldsa_rej_ntt_poly`'s contract `rnK` says. -/
def r4K : Contract isa where
  pre := sample4K.pre
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 4).all (fun k => (rnFold [] (G (seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256)
          then 1 else 0) ∧
      ∀ k < 4, (rnFold [] (G (seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 →
        PolyIs s'.mem (poly4 (s.gpr .rsi) k) (toPoly (rnFold [] (G (seed4 s.mem (s.gpr .rdi) k) 1008)))
  pub := sample4K.pub

/-- The coefficients of seed `k`'s whole output. -/
theorem Lt_336 (σ : State) (k : Nat) : Lt σ k 336 = rnFold [] (G (B σ k) 1008) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [Xb, G_length])]

theorem Lt_zero (σ : State) (k : Nat) : Lt σ k 0 = [] := by
  simp only [Lt, Nat.mul_zero, List.take_zero]; rfl

/-- 1 if each of the first `K` seeds has 256 coefficients, 0 otherwise. -/
def okN (σ : State) (K : Nat) : Nat := if (List.range K).all (fun k => (Lt σ k 336).length == 256) then 1 else 0

/-- Where the counts are kept. -/
abbrev jR (σ : State) : Region := ⟨at' σ oJ, 32⟩

/-- The saved registers. -/
abbrev svR (σ : State) : Region := ⟨at' σ oSave, 40⟩

section
variable {σ : State} (hp : Pre σ)
include hp

/-! ## The regions -/

omit hp in
theorem low_jR : (lowR σ).Disjoint (jR σ) :=
  Offset.base_disjoint (scr σ) (k := oSave) (e := oJ) (n := 32) (by simp only [oSave, oJ]; omega)
    (by simp only [oJ]; omega)

omit hp in
theorem sv_jR : (svR σ).Disjoint (jR σ) :=
  Offset.disjoint (scr σ) (d := oSave) (n := 40) (e := oJ) (k := 32) (.inl (by simp only [oSave, oJ]; omega))
    (by simp only [oSave]; omega) (by simp only [oJ]; omega)

theorem low_poly {K : Nat} (hK : K < 4) : (lowR σ).Disjoint (pR (poly4 (aP σ) K)) :=
  Region.Disjoint.sub_right (Region.Disjoint.sub_left hp.a_scr.symm (Region.sub_prefix (by simp only [oSave]; omega)))
    (sub_poly hK)

theorem sv_poly {K : Nat} (hK : K < 4) : (svR σ).Disjoint (pR (poly4 (aP σ) K)) :=
  scr_poly hp hK (a := oSave) (n := 40) (by simp only [oSave]; omega) _ (List.mem_singleton_self _)

theorem jR_poly {K : Nat} (hK : K < 4) : (jR σ).Disjoint (pR (poly4 (aP σ) K)) :=
  scr_poly hp hK (a := oJ) (n := 32) (by simp only [oJ]; omega) _ (List.mem_singleton_self _)

theorem poly_jR (k : Nat) (hk : k < 4) : (VG.Proof.MlDsa.Sample.polyR (poly4 (aP σ) k)).Disjoint (jR σ) :=
  (jR_poly hp hk).symm

/-! ## Frames -/

omit hp in
/-- `Env` after writes apart from the saved registers, in the regions of the precondition. -/
theorem env_frame {s s' : State} (he : EnvK σ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hsv : ∀ r ∈ rs, (svR σ).Disjoint r) (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) :
    EnvK σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, he.frame.trans (hf.sub hsub)⟩
  rw [hf.readW (Region.contains_self _ _) (fun r hr => (hsv r hr).sub_left
    (Offset.sub (scr σ) (d := oSave + 8 * i) (n := 8) (e := oSave) (k := 40) (by omega) (by omega))) (by decide)]
  exact he.saved i hi

omit hp in
/-- `SqT` after writes apart from the low scratch space and the saved registers. -/
theorem sqT_frame {t n : Nat} (hn : n ≤ 3) {s s' : State} (h : SqT σ t n s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hlow : ∀ r ∈ rs, (lowR σ).Disjoint r) (hsv : ∀ r ∈ rs, (svR σ).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r) : SqT σ t n s' := by
  refine ⟨env_frame h.env hf hsv hsub hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hg .r14 (by simp), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * (50 + r) + 8 * k) (by simp only [oSave]; omega))) (by decide)]
    exact h.rc r hr k hk
  · rw [hf.readW (Region.contains_self _ _) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := 32 * i + 8 * k) (by simp only [oSave]; omega))) (by decide)]
    exact h.lanes i hi k hk
  · rw [frame_byte hf (R := ⟨at' σ (oBuf + 504 * k + p), 1⟩) (fun r' hr' => (hlow r' hr').sub_left
      (Offset.sub_base (scr σ) (d := oBuf + 504 * k + p) (by simp only [oBuf, oSave]; omega)))
      (Region.contains_self _ _)]
    exact h.buf k hk p (by omega)

/-- A count, apart from writes to a polynomial. -/
theorem j_poly {K : Nat} (hK : K < 4) {m m' : Mem} (hf : Frame [pR (poly4 (aP σ) K)] m m') {k : Nat} (hk : k < 4) :
    m'.readW (at' σ (oJ + 8 * k)) 64 = m.readW (at' σ (oJ + 8 * k)) 64 :=
  hf.readW (Region.contains_self _ _) (scr_poly hp hK (a := oJ + 8 * k) (n := 8) (by simp only [oJ]; omega))
    (by decide)

omit hp in
/-- A stored polynomial, apart from writes to another one. -/
theorem st_poly {K k : Nat} (hK : K < 4) (hk : k < 4) (hne : k ≠ K) {m m' : Mem}
    (hf : Frame [pR (poly4 (aP σ) K)] m m') {L : List Zq} (h : Stored m (poly4 (aP σ) k) L) (hL : L.length ≤ 256) :
    Stored m' (poly4 (aP σ) k) L :=
  stored_frame hf (poly_poly hK hk hne) h hL

omit hp in
theorem sub_polyR {K : Nat} (hK : K < 4) : ∀ r ∈ [pR (poly4 (aP σ) K)], ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨aR σ, by simp, sub_poly hK⟩

omit hp in
theorem sub_jR : ∀ r ∈ [jR σ], ∃ R ∈ [aR σ, scrR σ, stkR σ], Region.Sub r R :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨scrR σ, by simp, sub_scr (by simp only [oJ]; omega)⟩

omit hp in
theorem jR_contains {k : Nat} (hk : k < 4) : (jR σ).Contains (at' σ (oJ + 8 * k)) 8 :=
  Offset.contains (scr σ) (d := oJ + 8 * k) (n := 8) (e := oJ) (k := 32) (by omega) (by omega) (by simp only [oJ]; omega)

omit hp in
theorem jR_write {k : Nat} (hk : k < 4) {m m' : Mem} (hf : Frame [jR σ] m m') (v : BitVec 64) :
    Frame [jR σ] m (m'.writeW (at' σ (oJ + 8 * k)) v) :=
  hf.writeW (List.mem_singleton_self _) v (jR_contains hk)

end

/-! ## The first halves -/

/-- After the first half of the seeds before `K`. -/
structure P1 (σ : State) (K : Nat) (s : State) : Prop where
  sq : SqT σ 0 3 s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k (if k < K then 168 else 0)).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k (if k < K then 168 else 0))

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem zeroJ_eq : zeroJ = [.mov32 .rax (.imm 0), .store (at_ .rbx (oJ + 8 * 0)) .rax, .store (at_ .rbx (oJ + 8 * 1)) .rax,
    .store (at_ .rbx (oJ + 8 * 2)) .rax, .store (at_ .rbx (oJ + 8 * 3)) .rax] := rfl

/-- The counts zeroed. -/
theorem zeroJ_ok {s : State} (h : SqT σ 0 3 s) : WP isa (.block zeroJ) s (P1 σ 0) := by
  have hin : ∀ k < 4, InRegions s.wr (at' σ (oJ + 8 * k)) 8 := fun k hk =>
    in_scr hp h.env.wr (by simp only [oJ]; omega)
  rw [zeroJ_eq]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = (((s.mem.writeW (at' σ (oJ + 8 * 0)) (0 : BitVec 64)).writeW
      (at' σ (oJ + 8 * 1)) (0 : BitVec 64)).writeW (at' σ (oJ + 8 * 2)) (0 : BitVec 64)).writeW (at' σ (oJ + 8 * 3))
      (0 : BitVec 64))
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide)
      xrun [h.env.rbx, h0, h1, h2, h3]
      rfl)
    (by decide)) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [jR σ] s.mem s'.mem := by
    rw [hm]
    exact jR_write (by decide) (jR_write (by decide) (jR_write (by decide) (jR_write (by decide) (Frame.refl _ _) _) _) _) _
  refine ⟨sqT_frame (by decide) h hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_jR) sub_jR k.2.1 k.2.2
    fun r hr => k.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide), fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm, ite_eq_right (by omega), Lt_zero, List.length_nil]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oJ, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [ite_eq_right (by omega), Lt_zero]
    exact stored_nil _ _

omit hp in
theorem hpre1 {K : Nat} (hK : K < 4) {s : State} (h : P1 σ K s) : HPre σ K 0 s :=
  ⟨h.sq.env, fun p hp' => by rw [h.sq.buf K hK p (by omega)],
    by rw [h.j K hK, ite_eq_right (by omega), Nat.mul_zero],
    by have := h.st K hK; rw [ite_eq_right (by omega)] at this; rwa [Nat.mul_zero]⟩

/-- `j` kept, after the first half of seed `K`. -/
theorem firstEnd_ok {K : Nat} (hK : K < 4) {s s₁ : State} (h : P1 σ K s) (hA : HAt σ s K 0 168 s₁) :
    WP isa (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) s₁ (P1 σ (K + 1)) := by
  have hin : InRegions s₁.wr (scr σ + BitVec.ofNat 64 (oJ + 8 * K)) 8 := in_scr hp hA.env.wr (by simp only [oJ]; omega)
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s₁.mem.writeW (at' σ (oJ + 8 * K)) (s₁.gpr .rdi))
    (by xrun [hA.env.rbx, hin]) rfl) fun s₂ ⟨hm, k⟩ => ?_
  have hf₂ : Frame [jR σ] s₁.mem s₂.mem := by
    rw [hm]; exact jR_write hK (Frame.refl _ _) _
  have k₁ : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s₁.gpr r = s.gpr r := fun r hr =>
    hA.kp.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨sqT_frame (by decide) (sqT_frame (by decide) h.sq hA.fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_poly hp hK)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_poly hp hK) (sub_polyR hK) hA.kp.2.1 hA.kp.2.2 k₁)
    hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_jR)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact sv_jR) sub_jR k.2.1 k.2.2 fun r hr => k.gpr (by simp),
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [Mem.readW_writeW_self64, hA.rdi, ite_eq_left (by omega)]
    · rw [rd64_off (by simp only [oJ]; omega) (by simp only [oJ]; omega) (by omega), j_poly hp hK hA.fr hk, h.j k hk]
      congr 3
      by_cases hk' : k < K
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]
  · have hL := Lt_length_le σ k (if k < K + 1 then 168 else 0)
    refine stored_frame hf₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact poly_jR hp k hk) ?_ hL
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega)]
      exact hA.stored
    · have := st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

/-- The first half of seed `K`. -/
theorem first_ok {K : Nat} (hK : K < 4) {s : State} (h : P1 σ K s) : WP isa (first K) s (P1 σ (K + 1)) :=
  WP.seq (WP.mono (half_ok hp hK (by decide) (hpre1 hK h)) fun _ hA => firstEnd_ok hp hK h hA)

end


/-! ## The second halves -/

/-- After the second half of the seeds before `K`. -/
structure P2 (σ : State) (K : Nat) (s : State) : Prop where
  env : EnvK σ s
  r14 : s.gpr .r14 = BitVec.ofNat 64 (okN σ K)
  buf : ∀ k < 4, ∀ p < 504, s.mem (at' σ (oBuf + 504 * k + p)) = xofByte (B σ k) (504 + p)
  j : ∀ k < 4, K ≤ k → s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k (if k < K then 336 else 168))

theorem tail_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rdi), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]) s fun s' =>
      (s'.gpr .r14 = BitVec.setWidth 64 ((s.gpr .r14).setWidth 32 &&& ((s.gpr .rdi) >>> 8).setWidth 32) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r14] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- Whether a count is 256, from its bit 8. -/
theorem full_bit {n : Nat} (hn : n ≤ 256) :
    (BitVec.ofNat 64 n >>> 8).setWidth 32 = if n == 256 then 1 else 0 := by
  by_cases e : n = 256
  · subst e; decide
  · rw [ite_eq_right (by simpa using e)]
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [h0]
    omega

theorem okN_succ (σ : State) (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (okN σ K)).setWidth 32 &&&
    (BitVec.ofNat 64 (Lt σ K 336).length >>> 8).setWidth 32) = BitVec.ofNat 64 (okN σ (K + 1)) := by
  rw [full_bit (Lt_length_le σ K 336)]
  simp only [okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range K).all fun k => (Lt σ k 336).length == 256 <;>
    cases (Lt σ K 336).length == 256 <;> rfl

section
variable {σ : State} (hp : Pre σ)
include hp

/-- During the second squeezes: the counts and coefficients of the first halves. -/
structure M2 (σ : State) (n : Nat) (s : State) : Prop where
  sq : SqT σ 3 n s
  j : ∀ k < 4, s.mem.readW (at' σ (oJ + 8 * k)) 64 = BitVec.ofNat 64 (Lt σ k 168).length
  st : ∀ k < 4, Stored s.mem (poly4 (aP σ) k) (Lt σ k 168)

omit hp in
theorem m2_of {s : State} (h : P1 σ 4 s) : M2 σ 0 s :=
  ⟨⟨h.sq.env, h.sq.r14, h.sq.rc, h.sq.lanes, fun _ _ p hp' => absurd hp' (by omega)⟩,
    fun k hk => by rw [h.j k hk, ite_eq_left hk], fun k hk => by have := h.st k hk; rwa [ite_eq_left hk] at this⟩

/-- A second squeeze. -/
theorem sqM_ok {n : Nat} (hn : n < 3) {s : State} (h : M2 σ n s) : WP isa (squeeze4 n) s (M2 σ (n + 1)) := by
  refine WP.mono (sqT_ok hp hn h.sq) fun s' ⟨q, hf⟩ => ⟨q, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.base_disjoint (scr σ) (k := oSave) (e := oJ + 8 * k) (n := 8) (by simp only [oSave, oJ]; omega)
        (by simp only [oJ]; omega)).symm) (by decide), h.j k hk]
  · exact stored_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact (low_poly hp hk).symm) (h.st k hk)
      (Lt_length_le σ k _)

omit hp in
/-- `vzeroupper`, after the second squeezes. -/
theorem vz_ok {s : State} (h : M2 σ 3 s) : WP isa (.block [.vop .vzeroupper]) s (P2 σ 0) := by
  refine WP.mono (WP.keep [] (Q := fun s' => s'.mem = s.mem) (by xrun; rfl) rfl) fun s' ⟨hm, k⟩ => ?_
  refine ⟨h.sq.env.keep hm k (by simp), by rw [k.gpr (by simp), h.sq.r14]; rfl, fun k hk p hp' => ?_,
    fun k hk _ => by rw [hm]; exact h.j k hk, fun k hk => ?_⟩
  · rw [hm, h.sq.buf k hk p (by omega)]
  · rw [ite_eq_right (by omega), hm]; exact h.st k hk

omit hp in
theorem hpre2 {K : Nat} (hK : K < 4) {s : State} (h : P2 σ K s) : HPre σ K 1 s :=
  ⟨h.env, fun p hp' => by rw [h.buf K hK p hp'], by rw [h.j K hK (Nat.le_refl _), Nat.mul_one],
    by have := h.st K hK; rw [ite_eq_right (by omega)] at this; rwa [Nat.mul_one]⟩

/-- The AND of whether seed `K` has 256 coefficients, after its second half. -/
theorem secondEnd_ok {K : Nat} (hK : K < 4) {s s₁ : State} (h : P2 σ K s) (hA : HAt σ s K 1 168 s₁) :
    WP isa (.block [.mov .rax (.reg .rdi), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]) s₁ (P2 σ (K + 1)) := by
  refine WP.mono (tail_ok s₁) fun s₂ ⟨⟨h14, hm⟩, k⟩ => ?_
  have hf : Frame [pR (poly4 (aP σ) K)] s.mem s₂.mem := by rw [hm]; exact hA.fr
  have hrdi : s₁.gpr .rdi = BitVec.ofNat 64 (Lt σ K 336).length := hA.rdi
  refine ⟨hA.env.keep hm k (by simp), ?_, fun k hk p hp' => ?_, fun k hk hKk => ?_, fun k hk => ?_⟩
  · rw [h14, hA.kp.gpr (by decide), h.r14, hrdi, okN_succ]
  · rw [frame_byte hf (R := ⟨at' σ (oBuf + 504 * k + p), 1⟩) (scr_poly hp hK (by simp only [oBuf]; omega))
      (Region.contains_self _ _)]
    exact h.buf k hk p hp'
  · rw [hm, j_poly hp hK hA.fr hk, h.j k hk (by omega)]
  · rw [hm]
    by_cases e : k = K
    · subst e
      rw [ite_eq_left (by omega)]
      exact hA.stored
    · have := st_poly hK hk e hA.fr (h.st k hk) (Lt_length_le σ k _)
      by_cases hk' : k < K
      · rw [ite_eq_left hk'] at this; rwa [ite_eq_left (by omega)]
      · rw [ite_eq_right hk'] at this; rwa [ite_eq_right (by omega)]

/-- The second half of seed `K`. -/
theorem second_ok {K : Nat} (hK : K < 4) {s : State} (h : P2 σ K s) : WP isa (second K) s (P2 σ (K + 1)) :=
  WP.seq (WP.mono (half_ok hp hK (by decide) (hpre2 hK h)) fun _ hA => secondEnd_ok hp hK h hA)

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {s : State} (h : P2 σ 4 s) :
    WP isa (.block epi) s fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, okN]
    simp only [Lt_336]
    split <;> rfl
  · rw [hm]
    have := h.st k hk
    rw [ite_eq_left hk, Lt_336] at this
    exact stored_polyIs this e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

/-- Everything after the prologue, the round constants and the padded seeds. -/
theorem body_ok {s : State} (h : SqInv σ 0 s) :
    WP isa (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block zeroJ)
      (.seq (first 0) (.seq (first 1) (.seq (first 2) (.seq (first 3)
        (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block [.vop .vzeroupper])
          (.seq (second 0) (.seq (second 1) (.seq (second 2) (.seq (second 3) (.block epi))))))))))))))))) s
      fun s' => r4K.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (sqT_ok hp (by decide) (sqT_of h)) fun s₁ ⟨q₁, _⟩ => WP.seq (WP.mono
    (sqT_ok hp (by decide) q₁) fun s₂ ⟨q₂, _⟩ => WP.seq (WP.mono (sqT_ok hp (by decide) q₂) fun s₃ ⟨q₃, _⟩ =>
      WP.seq (WP.mono (zeroJ_ok hp q₃) fun s₄ p₀ => ?_))))
  refine WP.seq (WP.mono (first_ok hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (first_ok hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (first_ok hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (first_ok hp (by decide) p₃) fun _ p₄ => ?_))))
  refine WP.seq (WP.mono (sqM_ok hp (by decide) (m2_of p₄)) fun _ m₁ => WP.seq (WP.mono (sqM_ok hp (by decide) m₁)
    fun _ m₂ => WP.seq (WP.mono (sqM_ok hp (by decide) m₂) fun _ m₃ => WP.seq (WP.mono (vz_ok m₃) fun _ r₀ => ?_))))
  exact WP.seq (WP.mono (second_ok hp (by decide) r₀) fun _ r₁ => WP.seq (WP.mono (second_ok hp (by decide) r₁)
    fun _ r₂ => WP.seq (WP.mono (second_ok hp (by decide) r₂) fun _ r₃ =>
      WP.seq (WP.mono (second_ok hp (by decide) r₃) fun _ r₄ => end_ok hp r₄))))

end

theorem correct (σ : State) (hs : r4K.pre σ) :
    ∃ t s', Exec isa rejNTT4Avx2 σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (start_ok hp) fun _ h => body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlDsa.X86_64.Rej4
