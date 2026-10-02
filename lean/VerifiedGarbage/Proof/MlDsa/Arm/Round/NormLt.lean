import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_norm_lt`

The loop body is symbolically executed once for any state (`body_ok`): a
coefficient `a` is bad when `bound ≤ a` and `bound ≤ q - a` (the carries of
the two comparisons), and `r4` becomes 1 at the first bad one (`acc`); the
result `1 - r4` is 1 exactly when no coefficient is bad, that is when the norm
is less than `bound` (`normRq_lt`, `normZq_lt`).
-/

namespace VG.Proof.MlDsa.Arm.Round.NormLt

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced normRq normZq)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving Qw loadQ_val)

/-! ## The body -/

/-- 1 if the coefficient `a` is bad for the bound `b`, 0 otherwise. -/
def bad (a b : BitVec 32) : BitVec 32 :=
  (if b.toNat ≤ a.toNat then 1 else 0) &&& (if b.toNat ≤ (Qw - a).toNat then 1 else 0)

section
variable {s : State} {x b c v : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = b) (h2 : s.gpr .r2 = c)
  (h4 : s.gpr .r4 = v) (iF : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h4 iF

theorem body_ok :
    WP isa (.block nlBody) s fun s' =>
      s'.gpr .r4 = v ||| bad (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32) b ∧ s'.gpr .r0 = x + 4 ∧
      s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ s'.mem = s.mem ∧
      (∀ r ∈ [Reg.r1, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [nlBody, bad, loadQ_val, h0, h1, h2, h4, iF, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_self, and_true]
  have z : ∀ y : BitVec 32, (0 : BitVec 32) + 0 + y = y := fun y => by bv_omega
  simp only [decide_eq_true_eq, z]

end

/-- Whether coefficient `a` has `‖a‖∞ < b`. -/
abbrev Ok (a b : BitVec 32) : Prop := a.toNat < b.toNat ∨ q - a.toNat < b.toNat

theorem bad_eq {a : BitVec 32} (ha : a.toNat < q) (b : BitVec 32) :
    bad a b = if Ok a b then 0 else 1 := by
  have e : (Qw - a).toNat = q - a.toNat := by rw [q_eq] at *; bv_omega
  unfold bad Ok
  rw [e]
  by_cases h1 : b.toNat ≤ a.toNat <;> by_cases h2 : b.toNat ≤ q - a.toNat <;>
    simp only [h1, h2, ite_true, ite_false] <;>
    first
    | (rw [ite_eq_right (by omega)]; decide)
    | (rw [ite_eq_left (by omega)]; decide)

/-- The accumulator after the first `i` coefficients of `m` at `F`. -/
def acc (m : Mem) (F : Addr) (b : BitVec 32) (i : Nat) : BitVec 32 :=
  if ∀ k < i, Ok (coeffAt m F k) b then 0 else 1

theorem acc_succ (m : Mem) (F : Addr) (b : BitVec 32) (i : Nat) :
    acc m F b i ||| (if Ok (coeffAt m F i) b then 0 else 1) = acc m F b (i + 1) := by
  have H : (∀ k < i + 1, Ok (coeffAt m F k) b) ↔ (∀ k < i, Ok (coeffAt m F k) b) ∧ Ok (coeffAt m F i) b :=
    ⟨fun h => ⟨fun k hk => h k (by omega), h i (by omega)⟩, fun ⟨h, h'⟩ k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      exacts [h k hk, h']⟩
  unfold acc
  by_cases h : ∀ k < i, Ok (coeffAt m F k) b <;> by_cases h' : Ok (coeffAt m F i) b <;>
    simp only [H, h', and_true, and_false, ite_true, ite_false] <;>
    first | (rw [ite_eq_left h]; decide) | (rw [ite_eq_right h]; decide)

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 4 ≤ s.sp.toNat
  rd : s.rd = [pR (P s .r0)]
  wr : s.wr = []
  s0 : (belowA s.sp 4).Disjoint (pR (P s .r0))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (P s .r0)

theorem pre_of {s : State} (h : (Spec.MlDsa.normLtContract Arm.abi 4).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The registers the loop keeps. -/
abbrev fixedR : List Reg := [.r1, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem loop {s s₁ : State} (hp : PreE s) (hE : Entry 4 s s₁) {s₂ : State} (hg : ∀ r, r ≠ .r4 → s₂.gpr r = s₁.gpr r)
    (h4 : s₂.gpr .r4 = 0) (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (_hwr : s₂.wr = s₁.wr) (hsp : s₂.sp = s₁.sp) :
    WP isa (mapLoop .r2 nlBody) s₂ fun s' => (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧
      s'.mem = s₁.mem ∧ s'.gpr .r4 = acc s.mem (P s .r0) (s.gpr .r1) 256 := by
  have g0 : s₂.gpr .r0 = s.gpr .r0 := (hg .r0 (by decide)).trans (congrFun hE.gpr _)
  have e : P s₂ .r0 = P s .r0 := by simp only [P, g0]
  have hL : Layout s₂ [.r0] [] := ⟨fun p hp' => by
      simp only [List.mem_singleton] at hp'; subst hp'; rw [hrd, hE.rd, e, hp.rd]; simp,
    fun _ h => (List.not_mem_nil h).elim, fun _ _ _ h => (List.not_mem_nil h).elim, List.Pairwise.nil,
    fun p hp' => by simp only [List.append_nil, List.mem_singleton] at hp'; subst hp'; rw [g0]; exact hp.f0⟩
  have eT : ∀ k < 256, coeffAt s₂.mem (P s₂ .r0) k = coeffAt s.mem (P s .r0) k := fun k hk => by
    rw [e, hm]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.s0.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok (ptrs := [.r0]) (fixed := fixedR) (V := fun _ _ => 0)
    (J := fun i s' => s'.gpr .r4 = acc s.mem (P s .r0) (s.gpr .r1) i) hL (by decide) (by decide)
    (fun s' hs' _ => by
      rw [hs']; simp only [show Reg.r4 ≠ Reg.r2 by decide, ite_false, h4]
      unfold acc; rw [ite_eq_left fun k hk => absurd hk (Nat.not_lt_zero k)])
    fun i hi s' hI => ?_)
    fun s' hI => ⟨fun r hr => (hI.fixed r hr).trans ((hg r (by revert r; decide)).trans (congrFun hE.gpr r)),
      hI.sp.trans hsp, ?_, hI.j⟩
  · have g1 : s'.gpr .r1 = s.gpr .r1 :=
      (hI.fixed .r1 (by decide)).trans ((hg .r1 (by decide)).trans (congrFun hE.gpr _))
    refine WP.mono (body_ok rfl g1 rfl hI.j (hI.inR hL hi (by simp) (by simp)))
      fun s'' ⟨r4, r0, r2, hz, hm', hf, rd, wr, sp⟩ => ⟨by rw [hm']; rfl, ?_, r2, hz, hf, rd, wr, sp, ?_⟩
    · intro p hp'; simp only [List.mem_singleton] at hp'; subst hp'; exact r0
    · show s''.gpr .r4 = _
      rw [r4, hI.read hL hi (by simp) (by simp), eT i hi, bad_eq (hp.red i (by rw [n_eq]; exact hi)), acc_succ]
  · have := hI.frame; simp only [List.map_nil] at this
    funext x; rw [← hm]; exact this x (fun _ h => (List.not_mem_nil h).elim)

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.normLt s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.gpr .r0 = if normRq [polyAt s.mem (P s .r0)] < (s.gpr .r1).toNat then 1 else 0 := by
  refine WP.mono (wp_saving [.r4] _ (W := [])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧
      s₂.gpr .r0 = if normRq [polyAt s.mem (P s .r0)] < (s.gpr .r1).toNat then 1 else 0)
    s hp.sp (fun _ h => (List.not_mem_nil h).elim) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, h0⟩, _, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, by rw [hg .r0]; exact h0⟩
  refine WP.seq (WP.of_runBlock ⟨_, runBlock_cons.trans (by rfl), ?_⟩)
  refine WP.seq (WP.mono (loop hp hE (s₂ := s₁.setReg .r4 0) (fun r hr => by simp [State.setReg, hr])
    (by simp [State.setReg]) rfl rfl rfl rfl) fun s₃ ⟨hf, hsp, hm, h4⟩ => ?_)
  run_block [h4]
  refine ⟨fun x _ => by rw [hm], fun r hr => ?_, ?_⟩
  · have : r ≠ .r0 := by revert r; decide
    rw [ite_eq_right this, ite_eq_right this]; exact hf r hr
  · have hn := normRq_lt (polyAt s.mem (P s .r0)) (s.gpr .r1).toNat
    unfold acc
    by_cases h : ∀ k < 256, Ok (coeffAt s.mem (P s .r0) k) (s.gpr .r1)
    · rw [ite_eq_left h, ite_eq_left (hn.mpr fun i hi => ?_)]
      · rfl
      · rw [normZq_lt, polyAt_val hp.red hi]; exact h i (by rw [n_eq] at hi; exact hi)
    · rw [ite_eq_right h, ite_eq_right fun h' => h fun k hk => ?_]
      · rfl
      · have := (normZq_lt _ _).mp (hn.mp h' k (by rw [n_eq]; exact hk))
        rwa [polyAt_val hp.red (by rw [n_eq]; exact hk)] at this

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Round.normLt (Spec.MlDsa.normLtContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4] _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32, h]
    rfl
  · sig_pub [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h0
    · simpa using h1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.normLtContract, Spec.MlDsa.normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.NormLt
