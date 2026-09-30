import VerifiedGarbage.Proof.MlDsa.Arm.Round.Hb
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_make_hint`

Untrusted: everything here is checked by Lean. The loop body is
symbolically executed once for each value of `γ₂` (`body_ok`): the hint is
`(r₁(r) ⊕ r₁(r + z mod q) + 63) >> 6`, 1 exactly when the two differ, as
both are less than 64 (`bmh_val`, from `makeHint_eq`), and `r4` counts the
1s (`onesFrom`). `γ₂` selects one of two loops, in the frames that save
`r4`–`r6`.
-/

namespace VG.Proof.MlDsa.Arm.Round.MakeHint

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced HintIs hintOnes gamma2s makeHint)
open VG.Proof.MlDsa.Arm.Arith.AddSub (fixS)
open VG.Impl.MlDsa.Arm.Arith (fixupS subQ)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving)

/-! ## Values -/

/-- What the body stores, for the words `z` and `r`. -/
def bmh (g : Nat) (z r : BitVec 32) : BitVec 32 :=
  ((bhb g (fixS (r + z - 0x800000 + 0x2000 - 1)) ^^^ bhb g r) + 63) >>> 6

theorem sumq_val {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (fixS (r + z - 0x800000 + 0x2000 - 1)).toNat = (r.toNat + z.toNat) % q := by
  rw [VG.Proof.MlDsa.Arm.Arith.AddSub.fixS_add hr hz]

theorem bmh_val {g : Nat} (hg : G2 g) (z r : Zq) :
    bmh g (BitVec.ofNat 32 z.val) (BitVec.ofNat 32 r.val) = (makeHint g z r).toNat := by
  have hz : z.val < 8380417 := z.isLt
  have hr : r.val < 8380417 := r.isLt
  have ez : (BitVec.ofNat 32 z.val).toNat = z.val := by rw [BitVec.toNat_ofNat]; omega
  have er : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega
  have hs := sumq_val (z := BitVec.ofNat 32 z.val) (r := BitVec.ofNat 32 r.val) (by rw [ez]; exact z.isLt)
    (by rw [er]; exact r.isLt)
  rw [ez, er] at hs
  have hsq : (r.val + z.val) % q < q := Nat.mod_lt _ (by decide)
  have h1 := bhb_toNat hg (a := fixS (BitVec.ofNat 32 r.val + BitVec.ofNat 32 z.val - 0x800000 + 0x2000 - 1))
    (by rw [hs]; exact hsq)
  have h2 := bhb_toNat hg (a := BitVec.ofNat 32 r.val) (by rw [er]; exact r.isLt)
  rw [hs] at h1
  rw [er] at h2
  have hm : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  have hm0 : 0 < hbM g := by rcases hg with rfl | rfl <;> decide
  rw [makeHint_eq hg.mem]
  unfold bmh
  generalize bhb g (fixS _) = X at h1
  generalize bhb g (BitVec.ofNat 32 r.val) = Y at h2
  have hX : X.toNat < 64 := by rw [h1]; have := Nat.mod_lt (hbF g ((r.val + z.val) % q)) hm0; omega
  have hY : Y.toNat < 64 := by rw [h2]; have := Nat.mod_lt (hbF g r.val) hm0; omega
  have hxy : (X ^^^ Y).toNat < 64 := by
    rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 6) hX hY
  have e : (X ^^^ Y = 0) ↔ X = Y := by
    constructor
    · intro h
      rw [← BitVec.xor_zero (x := X), ← BitVec.xor_self (x := Y), ← BitVec.xor_assoc, h]; exact BitVec.zero_xor
    · intro h; subst h; simp
  by_cases h : hbF g r.val % hbM g = hbF g ((r.val + z.val) % q) % hbM g
  · have hXY : X = Y := BitVec.eq_of_toNat_eq (by rw [h1, h2, h])
    rw [e.mpr hXY, decide_eq_false (fun h' => h' h)]
    rfl
  · have hXY : X ^^^ Y ≠ 0 := fun h' => h (by rw [← h2, ← h1, e.mp h'])
    rw [decide_eq_true h]
    have : (X ^^^ Y).toNat ≠ 0 := fun h' => hXY (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    generalize X ^^^ Y = W at hxy this
    show _ = (1 : BitVec 32)
    bv_omega

/-! ## The body -/

section
variable {s : State} {x0 x1 x3 c v : BitVec 32} (h0 : s.gpr .r0 = x0) (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = c)
  (h3 : s.gpr .r3 = x3) (h4 : s.gpr .r4 = v)
  (iZ : InRegions (s.rd ++ s.wr) (State.addr (x0 + BitVec.ofNat 32 0)) 4)
  (iR : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4)
  (oH : InRegions s.wr (State.addr (x3 + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 iZ iR oH

theorem body_ok {g : Nat} (hg : G2 g) :
    WP isa (.block (mhBody g)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x3 + BitVec.ofNat 32 0))
        (bmh g (s.mem.readW (State.addr (x0 + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r4 = v + bmh g (s.mem.readW (State.addr (x0 + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32) ∧
      s'.gpr .r0 = x0 + 4 ∧ s'.gpr .r1 = x1 + 4 ∧ s'.gpr .r3 = x3 + 4 ∧ s'.gpr .r2 = c - 1 ∧
      s'.z = (c - 1 == 0) ∧ (∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rcases hg with rfl | rfl <;>
  · run_block [mhBody, hb, hbRaw, csubM, addMaskM, subQ, fixupS, tail013, bmh, fixS, bhb, bcsubM, bhbRaw,
      h0, h1, h2, h3, h4, iZ, iR, oH, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_self, and_true]

end

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 12 ≤ s.sp.toNat
  rd : s.rd = [pR (P s .r0), pR (P s .r1)]
  wr : s.wr = [pR (P s .r3)]
  d0 : (pR (P s .r0)).Disjoint (pR (P s .r3))
  d1 : (pR (P s .r1)).Disjoint (pR (P s .r3))
  s0 : (belowA s.sp 12).Disjoint (pR (P s .r0))
  s1 : (belowA s.sp 12).Disjoint (pR (P s .r1))
  s3 : (belowA s.sp 12).Disjoint (pR (P s .r3))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32
  g : (s.gpr .r2).toNat ∈ gamma2s
  redZ : Reduced s.mem (P s .r0)
  redR : Reduced s.mem (P s .r1)

theorem pre_of {s : State} (h : (Spec.MlDsa.makeHintContract Arm.abi 12).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- The registers the loops keep. -/
abbrev fixedR : List Reg := [.r7, .r8, .r9, .r10, .r11, .lr]

/-- The hint of the polynomials on entry. -/
abbrev hint (s : State) (g : Nat) : Vector Bool n :=
  Vector.zipWith (makeHint g) (polyAt s.mem (P s .r0)) (polyAt s.mem (P s .r1))

theorem hint_word {s : State} (hp : PreE s) {g : Nat} (hg : G2 g) {k : Nat} (hk : k < 256) :
    bmh g (coeffAt s.mem (P s .r0) k) (coeffAt s.mem (P s .r1) k) = ((hint s g)[k]!).toNat := by
  have hk' : k < n := by rw [n_eq]; exact hk
  rw [zipWith_get _ _ _ hk', polyAt_get _ _ hk', polyAt_get _ _ hk', ← bmh_val hg,
    word_of_reduced (hp.redZ k hk'), word_of_reduced (hp.redR k hk')]

theorem loop {s s₁ s₂ : State} (hp : PreE s) (hE : Entry 12 s s₁) {g : Nat} (hg : G2 g)
    (hg₂ : ∀ r, r ≠ .r4 → s₂.gpr r = s.gpr r) (h4 : s₂.gpr .r4 = 0) (hm : s₂.mem = s₁.mem)
    (hrd : s₂.rd = s₁.rd) (hwr : s₂.wr = s₁.wr) (hsp : s₂.sp = s₁.sp) :
    WP isa (mapLoop .r2 (mhBody g)) s₂ fun s' => (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧
      Frame [pR (P s .r3)] s₁.mem s'.mem ∧ (s'.gpr .r4).toNat = onesFrom (hint s g) 0 ∧
      ∀ k < 256, coeffAt s'.mem (P s .r3) k = ((hint s g)[k]!).toNat := by
  have e : ∀ r, r ≠ .r4 → P s₂ r = P s r := fun r hr => by simp only [P, hg₂ r hr]
  have hL : Layout s₂ [.r0, .r1] [.r3] := by
    refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, List.pairwise_singleton _ _, fun p hp' => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> rw [e _ (by decide), hrd, hE.rd, hp.rd] <;> simp
    · simp only [List.mem_singleton] at ho; subst ho
      rw [e _ (by decide), hwr]; exact hE.wr _ (by rw [hp.wr]; simp)
    · simp only [List.mem_singleton] at ho; subst ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> rw [e _ (by decide), e _ (by decide)]
      exacts [hp.d0, hp.d1]
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> rw [hg₂ _ (by decide)]
      exacts [hp.f0, hp.f1, hp.f3]
  have eIn : ∀ p, p = .r0 ∨ p = .r1 → ∀ k < 256, coeffAt s₂.mem (P s₂ p) k = coeffAt s.mem (P s p) k := by
    intro p hp' k hk
    have hd : (belowA s.sp 12).Disjoint (pR (P s p)) := by rcases hp' with rfl | rfl; exacts [hp.s0, hp.s1]
    rw [e p (by rcases hp' with rfl | rfl <;> decide), hm]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hd.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok (ptrs := [.r0, .r1, .r3]) (fixed := fixedR)
    (V := fun _ i => bmh g (coeffAt s₂.mem (P s₂ .r0) i) (coeffAt s₂.mem (P s₂ .r1) i))
    (J := fun i s' => (s'.gpr .r4).toNat + onesFrom (hint s g) i = onesFrom (hint s g) 0 ∧ (s'.gpr .r4).toNat ≤ i)
    hL (by decide) (by decide) (fun s' hs' _ => ?_) fun i hi s' hI => ?_) fun s' hI => ⟨fun r hr => ?_, ?_, ?_,
      ?_, fun k hk => ?_⟩
  · rw [hs']; simp only [show Reg.r4 ≠ Reg.r2 by decide, ite_false, h4]
    exact ⟨Nat.zero_add _, Nat.zero_le _⟩
  · refine WP.mono (body_ok rfl rfl rfl rfl rfl (hI.inR hL hi (by simp) (by simp)) (hI.inR hL hi (by simp) (by simp))
      (hI.inW hL hi (by simp) (by simp)) hg)
      fun s'' ⟨hm', r4, r0, r1, r3, r2, hz, hf, rd, wr, sp⟩ => ⟨?_, ?_, r2, hz, hf, rd, wr, sp, ?_⟩
    · rw [hm', hI.read hL hi (by simp) (by simp), hI.read hL hi (p := .r1) (by simp) (by simp),
        hI.addr hL hi (p := .r3) (by simp) (by simp)]; rfl
    · intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      exacts [r0, r1, r3]
    · rw [hI.read hL hi (by simp) (by simp), hI.read hL hi (p := .r1) (by simp) (by simp), eIn _ (.inl rfl) i hi,
        eIn _ (.inr rfl) i hi, hint_word hp hg hi] at r4
      obtain ⟨hj, hle⟩ := hI.j
      have hs := onesFrom_step (hint s g) (lo := i) (by rw [n_eq]; exact hi)
      have hb : ((hint s g)[i]!).toNat ≤ 1 := by cases (hint s g)[i]! <;> decide
      have ht : (s''.gpr .r4).toNat = (s'.gpr .r4).toNat + ((hint s g)[i]!).toNat := by
        rw [r4]
        have : ((((hint s g)[i]!).toNat : Nat) : BitVec 32).toNat = ((hint s g)[i]!).toNat := by
          rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]; omega
        rw [BitVec.toNat_add, this]; omega
      exact ⟨by omega, by omega⟩
  · rw [hI.fixed r hr, hg₂ r (by revert r; decide)]
  · rw [hI.sp, hsp]
  · have := hI.frame; simp only [List.map_cons, List.map_nil] at this
    rw [e .r3 (by decide), hm] at this; exact this
  · have := hI.j.1; simp only [onesFrom_n, Nat.add_zero] at this; exact this
  · rw [← e _ (by decide), hI.done .r3 (by simp) k hk, eIn _ (.inl rfl) k hk, eIn _ (.inr rfl) k hk,
      hint_word hp hg hk]

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.makeHint s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      HintIs s'.mem (P s .r3) 1 [hint s (s.gpr .r2).toNat] ∧
      (s'.gpr .r0).toNat = hintOnes [hint s (s.gpr .r2).toNat] := by
  have hG : G2 (s.gpr .r2).toNat := (mem_gamma2s hp.g).elim .inr .inl
  refine WP.mono (wp_saving [.r4, .r5, .r6] _ (W := [pR (P s .r3)])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧ HintIs s₂.mem (P s .r3) 1 [hint s (s.gpr .r2).toNat] ∧
      (s₂.gpr .r0).toNat = hintOnes [hint s (s.gpr .r2).toNat])
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.s3) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hh, h0⟩, hm, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, hm ▸ hh, by rw [hg .r0]; exact h0⟩
  have he : encodable (BitVec.ofNat 32 g88) = true := by decide
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [gammaCmp, runBlock_cons, runStep_some, exec, Op2.eval, he, ite_true, Option.map_some]
    rfl, ?_⟩)
  have hz := VG.Proof.MlKem.Arm.cmp_z (s₁.gpr .r2) g88 (by decide)
  have hloop : ∀ g, G2 g → g = (s.gpr .r2).toNat → WP isa (mapLoop .r2 (mhBody g))
      ((subFlags s₁ (s₁.gpr .r2) (BitVec.ofNat 32 g88)).setReg .r4 0) fun s' =>
        (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧ Frame [pR (P s .r3)] s₁.mem s'.mem ∧
        (s'.gpr .r4).toNat = onesFrom (hint s (s.gpr .r2).toNat) 0 ∧
        ∀ k < 256, coeffAt s'.mem (P s .r3) k = ((hint s (s.gpr .r2).toNat)[k]!).toNat := fun g hg eg => by
    subst eg
    exact loop hp hE hg (fun r hr => by simp [State.setReg, hr, subFlags, hE.gpr]) (by simp [State.setReg])
      rfl rfl rfl rfl
  refine WP.seq (WP.mono
    (WP.ite (decide ((s₁.gpr .r2).toNat = g88)) (by simp only [eval, subFlags, State.setReg, hz])
      (fun h => hloop g88 (.inr rfl) (by rw [← of_decide_eq_true h, hE.gpr]))
      (fun h => hloop g32 (.inl rfl) (by
        have := of_decide_eq_false h
        rw [hE.gpr] at this
        rcases mem_gamma2s hp.g with h' | h'
        · exact absurd h' this
        · exact h'.symm))) fun s₃ ⟨hf, hsp, hfr, h4, hc⟩ => ?_)
  run_block []
  refine ⟨hfr, fun r hr => ?_, ?_, ?_⟩
  · have : r ≠ .r0 := by revert r; decide
    rw [ite_eq_right this]; exact hf r hr
  · exact hintIs_of_toNat fun j hj => hc j (by rw [n_eq] at hj; exact hj)
  · rw [hintOnes_single]; exact h4

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 95232 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Round.makeHint (Spec.MlDsa.makeHintContract Arm.abi 12) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4, .r5, .r6] _ [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hh, h0⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32]
    exact ⟨hh, h0⟩
  · sig_pub [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.MakeHint
