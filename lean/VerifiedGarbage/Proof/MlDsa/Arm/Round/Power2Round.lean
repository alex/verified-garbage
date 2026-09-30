import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_power2round`

Untrusted: everything here is checked by Lean. The loop body is
symbolically executed once for any state (`body_ok`); its values are
`Power2Round`'s (`t1_val`, `t0_val`, from `power2Round_eq`), and the loop
(`loop_ok`) in the frame that saves `r4` (`wp_saving`) writes them all.
-/

namespace VG.Proof.MlDsa.Arm.Round.P2R

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs NatPolyIs natPolyAt power2Round ofInt)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving)
open VG.Proof.MlDsa.Arm.Arith.AddSub (fixS)
open VG.Impl.MlDsa.Arm.Arith (fixupS)

/-! ## Values -/

/-- What the body stores to `t1`. -/
def bt1 (a : BitVec 32) : BitVec 32 := (a + 4096 - 1) >>> 13

/-- What the body stores to `t0`. -/
def bt0 (a : BitVec 32) : BitVec 32 := fixS ((a + 4096 - 1) <<< 19 >>> 19 - 4096 + 1)

theorem t1_val (r : Zq) : (bt1 (BitVec.ofNat 32 r.val)).toNat = (power2Round r).1.toNat := by
  rw [power2Round_eq]
  simp only [Int.toNat_natCast]
  have h := r.isLt
  generalize r.val = v at h ⊢
  rw [q_eq] at h
  unfold bt1
  bv_omega

theorem t0_val (r : Zq) : (bt0 (BitVec.ofNat 32 r.val)).toNat = (ofInt (power2Round r).2).val := by
  rw [power2Round_t0]
  have h := r.isLt
  generalize r.val = v at h ⊢
  rw [q_eq] at h ⊢
  unfold bt0 fixS
  split <;> bv_omega

/-! ## The body -/

section
variable {s : State} {x y w c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c)
  (iT : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
  (o0 : InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 iT o1 o0

theorem body_ok :
    WP isa (.block p2rBody) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
        (bt1 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))).writeW (State.addr (w + BitVec.ofNat 32 0))
        (bt0 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = w + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [p2rBody, fixupS, bt1, bt0, fixS, h0, h1, h2, h3, iT, o1, o0, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 4 ≤ s.sp.toNat
  rd : s.rd = [pR (P s .r0)]
  wr : s.wr = [pR (P s .r1), pR (P s .r2)]
  d01 : (pR (P s .r0)).Disjoint (pR (P s .r1))
  d02 : (pR (P s .r0)).Disjoint (pR (P s .r2))
  d12 : (pR (P s .r1)).Disjoint (pR (P s .r2))
  s0 : (belowA s.sp 4).Disjoint (pR (P s .r0))
  s1 : (belowA s.sp 4).Disjoint (pR (P s .r1))
  s2 : (belowA s.sp 4).Disjoint (pR (P s .r2))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (P s .r0)

theorem pre_of {s : State} (h : (Spec.MlDsa.power2RoundContract Arm.abi 4).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The registers the loop keeps. -/
abbrev fixedR : List Reg := [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The values the loop writes, from the memory `m` it starts with. -/
def val (s₁ : State) (o : Reg) (i : Nat) : BitVec 32 :=
  if o = .r1 then bt1 (coeffAt s₁.mem (P s₁ .r0) i) else bt0 (coeffAt s₁.mem (P s₁ .r0) i)

theorem layout {s s₁ : State} (hp : PreE s) (hE : Entry 4 s s₁) : Layout s₁ [.r0] [.r1, .r2] := by
  have g := hE.gpr
  have e : ∀ r, P s₁ r = P s r := fun r => by simp only [P, g]
  refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, ?_, fun p hp' => ?_⟩
  · simp only [List.mem_singleton] at hp'; subst hp'
    rw [e, hE.rd, hp.rd]; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rw [e] <;> exact hE.wr _ (by rw [hp.wr]; simp)
  · simp only [List.mem_singleton] at hp'; subst hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rw [e, e]
    exacts [hp.d01, hp.d02]
  · exact List.pairwise_pair.mpr (by rw [e, e]; exact hp.d12)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> rw [g]
    exacts [hp.f0, hp.f1, hp.f2]

theorem loop_body {s s₁ : State} (hp : PreE s) (hE : Entry 4 s s₁) :
    ∀ i < 256, ∀ s', Inv s₁ [.r0, .r1, .r2] fixedR [.r1, .r2] .r3 (val s₁) (fun _ _ => True) i s' →
      WP isa (.block p2rBody) s' (Step s₁ [.r0, .r1, .r2] fixedR [.r1, .r2] .r3 (val s₁) (fun _ _ => True) i s') := by
  intro i hi s' hI
  have hL := layout hp hE
  refine WP.mono (body_ok rfl rfl rfl rfl (hI.inR hL hi (by simp) (by simp))
    (hI.inW hL hi (by simp) (by simp)) (hI.inW hL hi (by simp) (by simp)))
    fun s'' ⟨hm, r0, r1, r2, r3, hz, hf, rd, wr, sp⟩ => ⟨?_, ?_, r3, hz, hf, rd, wr, sp, trivial⟩
  · rw [hm, hI.read hL hi (by simp) (by simp), hI.addr hL hi (p := .r1) (by simp) (by simp),
      hI.addr hL hi (p := .r2) (by simp) (by simp)]
    rfl
  · intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    exacts [r0, r1, r2]

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.power2Round s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ NatPolyIs s'.mem (P s .r1) ((polyAt s.mem (P s .r0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (P s .r2) ((polyAt s.mem (P s .r0)).map fun c => ofInt (power2Round c).2) := by
  refine WP.mono (wp_saving [.r4] _ (W := [pR (P s .r1), pR (P s .r2)])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧
      NatPolyIs s₂.mem (P s .r1) ((polyAt s.mem (P s .r0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s₂.mem (P s .r2) ((polyAt s.mem (P s .r0)).map fun c => ofInt (power2Round c).2))
    s hp.sp (fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      exacts [hp.s1, hp.s2]) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, h1, h0⟩, hm, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, hm ▸ h1, hm ▸ h0⟩
  have g := hE.gpr
  have e : ∀ r, P s₁ r = P s r := fun r => by simp only [P, g]
  have hL := layout hp hE
  have eT : ∀ k < 256, coeffAt s₁.mem (P s₁ .r0) k = coeffAt s.mem (P s .r0) k := fun k hk => by
    rw [e]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.s0.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok hL (by decide) (by decide) (fun _ _ _ => trivial) (loop_body hp hE))
    fun s₂ hI => ⟨?_, fun r hr => (hI.fixed r hr).trans (congrFun g r), ?_, ?_⟩
  · have := hI.frame; simp only [List.map_cons, List.map_nil] at this; rwa [e, e] at this
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [← e, hI.done .r1 (by simp) k hk, val, ite_eq_left rfl, map_get _ _ hk, polyAt_get _ _ hk, eT k hk,
      ← t1_val, word_of_reduced (hp.red k hk)]
  · refine polyIs_of_toNat fun k hk => ?_
    rw [← e, hI.done .r2 (by simp) k hk, val, ite_eq_right (by decide), map_get _ _ hk, polyAt_get _ _ hk,
      eT k hk, ← t0_val, word_of_reduced (hp.red k hk)]

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem verified :
    Verified Arm.target Impl.MlDsa.Arm.Round.power2Round (Spec.MlDsa.power2RoundContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4] _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h1, h0⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h1, h0⟩
  · sig_pub [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.power2RoundContract, Spec.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.P2R
