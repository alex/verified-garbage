import VerifiedGarbage.Proof.MlDsa.Arm.Round.Bits
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_use_hint`

The loop body is symbolically executed once for each value of `γ₂`
(`body_ok`); its value is `(f + m + δ) mod m` for the `δ` of `useHint_eq`
(`buh_val`): the carry of `f · 2γ₂ - a` is clear exactly when `f · 2γ₂ < a`,
and the hint word `h` is not 0 exactly when bit 31 of `(0 - h) | h` is set
(`nz_eq`). `γ₂` selects one of two loops, in the frames that save `r4`–`r6`.
-/

namespace VG.Proof.MlDsa.Arm.Round.UseHint

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced NatPolyIs hintAt gamma2s useHint)
open VG.Proof.MlDsa.Arm.Round.Bits (w2g w2g_val)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving)

/-! ## Values -/

/-- 1 if the word `h` is not 0, 0 if it is. -/
theorem nz_eq (h : BitVec 32) : ((0 - h) ||| h) >>> 31 = if h = 0 then 0 else 1 := by
  rw [BitVec.ushiftRight_or_distrib]
  by_cases e : h = 0
  · subst e; decide
  · rw [ite_eq_right e]
    have : h.toNat ≠ 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    by_cases h31 : h.toNat < 2 ^ 31
    · have a : (0 - h) >>> 31 = 1 := by bv_omega
      have b : h >>> 31 = 0 := by bv_omega
      rw [a, b]; rfl
    · have b : h >>> 31 = 1 := by bv_omega
      rw [b]
      have : (0 - h) >>> 31 = 0 ∨ (0 - h) >>> 31 = 1 := by bv_omega
      rcases this with a | a <;> rw [a] <;> rfl

/-- What the body stores, for the hint word `h` and the word `r`. -/
def buh (g : Nat) (h r : BitVec 32) : BitVec 32 :=
  bcsubM g (bcsubM g (bhbRaw g r +
    ((1 : BitVec 32) - (if r.toNat ≤ (w2g g * bhbRaw g r).toNat then (1 : BitVec 32) else 0) <<< 1) *
    (((0 - h) ||| h) >>> 31) + BitVec.ofNat 32 (dMod g)))

theorem bcsubM_toNat' {g : Nat} (hg : G2 g) {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    (bcsubM g x).toNat = if x.toNat < dMod g then x.toNat else x.toNat - dMod g := by
  unfold bcsubM
  rcases hg with rfl | rfl
  · rw [ite_eq_left (show g32 = 261888 from rfl), show dMod g32 = 16 from rfl]
    split <;> bv_omega
  · rw [ite_eq_right (show ¬g88 = 261888 by decide), show dMod g88 = 44 from rfl]
    split <;> bv_omega

theorem buh_val {g : Nat} (hg : G2 g) (hw : BitVec 32) (r : Zq) :
    (buh g hw (BitVec.ofNat 32 r.val)).toNat = (useHint g (decide (hw ≠ 0)) r).toNat := by
  have hr : r.val < 8380417 := r.isLt
  have er : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega
  have hF := bhbRaw_toNat hg (a := BitVec.ofNat 32 r.val) (by rw [er]; exact r.isLt)
  rw [er] at hF
  have hfle := hbF_le hg.mem r.isLt
  have hm := hbM_mul hg.mem
  have hMd := hbM_dMod hg
  have hm16 : 16 ≤ dMod g ∧ dMod g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  have hg' : 2 * g < 2 ^ 20 := by rcases hg with rfl | rfl <;> decide
  rw [useHint_eq hg.mem, Int.toNat_natCast]
  unfold buh
  rw [w2g_val hg, nz_eq]
  generalize bhbRaw g (BitVec.ofNat 32 r.val) = F at hF
  have hFm : (BitVec.ofNat 32 (2 * g) * F).toNat = hbF g r.val * (2 * g) := by
    rw [BitVec.toNat_mul, hF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * g) (by omega), Nat.mul_comm]
    have : hbF g r.val * (2 * g) ≤ hbM g * (2 * g) := Nat.mul_le_mul_right _ hfle
    rw [q_eq] at hm
    exact Nat.mod_eq_of_lt (by omega)
  rw [hFm, ← hMd]
  rw [hMd] at hfle ⊢
  generalize hbF g r.val = f at hF hfle hFm
  simp only [er]
  -- The value before the two conditional subtractions.
  have key : ∀ x : BitVec 32, x.toNat ≤ 2 * dMod g + 1 → dMod g - 1 ≤ x.toNat →
      (bcsubM g (bcsubM g x)).toNat = x.toNat % dMod g := fun x h1 h2 => by
    have hi := bcsubM_toNat' hg (x := x) (by omega)
    have hi2 := bcsubM_toNat' hg (x := bcsubM g x) (by rw [hi]; split <;> omega)
    rw [hi2, hi]
    by_cases c1 : x.toNat < dMod g
    · rw [ite_eq_left c1, ite_eq_left c1, Nat.mod_eq_of_lt c1]
    · rw [ite_eq_right c1]
      by_cases c2 : x.toNat - dMod g < dMod g
      · rw [ite_eq_left c2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt c2]
      · rw [ite_eq_right c2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
  by_cases h0 : hw = 0
  · rw [ite_eq_left h0, decide_eq_false (fun h => h h0)]
    simp only [Bool.false_eq_true, ite_false]
    have hx : (F + ((1 : BitVec 32) - (if r.val ≤ f * (2 * g) then (1 : BitVec 32) else 0) <<< 1) * 0 +
        BitVec.ofNat 32 (dMod g)).toNat = f + dMod g := by
      bv_omega
    rw [key _ (by rw [hx]; omega) (by rw [hx]; omega), hx]
  · rw [ite_eq_right h0, decide_eq_true h0]
    simp only [ite_true]
    by_cases hc : r.val ≤ f * (2 * g)
    · rw [ite_eq_left hc, ite_eq_right (by omega)]
      have hx : (F + ((1 : BitVec 32) - (1 : BitVec 32) <<< 1) * 1 + BitVec.ofNat 32 (dMod g)).toNat =
          f + dMod g - 1 := by
        rw [show ((1 : BitVec 32) - (1 : BitVec 32) <<< 1) * 1 = 4294967295 by decide]; bv_omega
      rw [key _ (by rw [hx]; omega) (by rw [hx]; omega), hx]
    · rw [ite_eq_right hc, ite_eq_left (by omega)]
      have hx : (F + ((1 : BitVec 32) - (0 : BitVec 32) <<< 1) * 1 + BitVec.ofNat 32 (dMod g)).toNat =
          f + dMod g + 1 := by
        rw [show ((1 : BitVec 32) - (0 : BitVec 32) <<< 1) * 1 = 1 by decide]; bv_omega
      rw [key _ (by rw [hx]; omega) (by rw [hx]; omega), hx]

/-! ## The body -/

theorem zz (y : BitVec 32) : (0 : BitVec 32) + 0 + y = y := by bv_omega

section
variable {s : State} {x0 x1 x3 c : BitVec 32} (h0 : s.gpr .r0 = x0) (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = c)
  (h3 : s.gpr .r3 = x3)
  (iH : InRegions (s.rd ++ s.wr) (State.addr (x0 + BitVec.ofNat 32 0)) 4)
  (iR : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4)
  (oO : InRegions s.wr (State.addr (x3 + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 iH iR oO

theorem body_ok {g : Nat} (hg : G2 g) :
    WP isa (.block (uhBody g)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x3 + BitVec.ofNat 32 0))
        (buh g (s.mem.readW (State.addr (x0 + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r0 = x0 + 4 ∧ s'.gpr .r1 = x1 + 4 ∧ s'.gpr .r3 = x3 + 4 ∧ s'.gpr .r2 = c - 1 ∧
      s'.z = (c - 1 == 0) ∧ (∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rcases hg with rfl | rfl <;>
  · run_block [uhBody, hbRaw, load2g, csubM, addMaskM, tail013, buh, bcsubM, bhbRaw, w2g, h0, h1, h2, h3, iH,
      iR, oO, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]
    all_goals simp only [zz, decide_eq_true_eq]
    all_goals rfl

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
  redR : Reduced s.mem (P s .r1)

theorem pre_of {s : State} (h : (Spec.MlDsa.useHintContract Arm.abi 12).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The registers the loops keep. -/
abbrev fixedR : List Reg := [.r7, .r8, .r9, .r10, .r11, .lr]

/-- The result on entry. -/
abbrev result (s : State) (g : Nat) : Vector Nat n :=
  Vector.zipWith (fun hj rj => (useHint g hj rj).toNat) ((hintAt s.mem (P s .r0) 1).headD (Vector.replicate n false))
    (polyAt s.mem (P s .r1))

theorem result_word {s : State} (hp : PreE s) {g : Nat} (hg : G2 g) {k : Nat} (hk : k < 256) :
    (buh g (coeffAt s.mem (P s .r0) k) (coeffAt s.mem (P s .r1) k)).toNat = (result s g)[k]! := by
  have hk' : k < n := by rw [n_eq]; exact hk
  rw [zipWith_get _ _ _ hk', hintAt_get _ _ hk', polyAt_get _ _ hk', ← buh_val hg,
    word_of_reduced (hp.redR k hk')]

theorem loop {s s₁ s₂ : State} (hp : PreE s) (hE : Entry 12 s s₁) {g : Nat} (hg : G2 g)
    (hg₂ : s₂.gpr = s.gpr) (hm : s₂.mem = s₁.mem) (hrd : s₂.rd = s₁.rd) (hwr : s₂.wr = s₁.wr)
    (hsp : s₂.sp = s₁.sp) :
    WP isa (mapLoop .r2 (uhBody g)) s₂ fun s' => (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧
      Frame [pR (P s .r3)] s₁.mem s'.mem ∧ ∀ k < 256, (coeffAt s'.mem (P s .r3) k).toNat = (result s g)[k]! := by
  have e : ∀ r, P s₂ r = P s r := fun r => by simp only [P, hg₂]
  have hL : Layout s₂ [.r0, .r1] [.r3] := by
    refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, List.pairwise_singleton _ _, fun p hp' => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> rw [e, hrd, hE.rd, hp.rd] <;> simp
    · simp only [List.mem_singleton] at ho; subst ho
      rw [e, hwr]; exact hE.wr _ (by rw [hp.wr]; simp)
    · simp only [List.mem_singleton] at ho; subst ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> rw [e, e]
      exacts [hp.d0, hp.d1]
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> rw [hg₂]
      exacts [hp.f0, hp.f1, hp.f3]
  have eIn : ∀ p, p = .r0 ∨ p = .r1 → ∀ k < 256, coeffAt s₂.mem (P s₂ p) k = coeffAt s.mem (P s p) k := by
    intro p hp' k hk
    have hd : (belowA s.sp 12).Disjoint (pR (P s p)) := by rcases hp' with rfl | rfl; exacts [hp.s0, hp.s1]
    rw [e p, hm]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hd.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok (ptrs := [.r0, .r1, .r3]) (fixed := fixedR)
    (V := fun _ i => buh g (coeffAt s₂.mem (P s₂ .r0) i) (coeffAt s₂.mem (P s₂ .r1) i))
    (J := fun _ _ => True) hL (by decide) (by decide) (fun _ _ _ => trivial) fun i hi s' hI => ?_)
    fun s' hI => ⟨fun r hr => by rw [hI.fixed r hr, hg₂], by rw [hI.sp, hsp], ?_, fun k hk => ?_⟩
  · refine WP.mono (body_ok rfl rfl rfl rfl (hI.inR hL hi (by simp) (by simp)) (hI.inR hL hi (by simp) (by simp))
      (hI.inW hL hi (by simp) (by simp)) hg)
      fun s'' ⟨hm', r0, r1, r3, r2, hz, hf, rd, wr, sp⟩ => ⟨?_, ?_, r2, hz, hf, rd, wr, sp, trivial⟩
    · rw [hm', hI.read hL hi (by simp) (by simp), hI.read hL hi (p := .r1) (by simp) (by simp),
        hI.addr hL hi (p := .r3) (by simp) (by simp)]; rfl
    · intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      exacts [r0, r1, r3]
  · have := hI.frame; simp only [List.map_cons, List.map_nil] at this
    rw [e .r3, hm] at this; exact this
  · rw [← e, hI.done .r3 (by simp) k hk, eIn _ (.inl rfl) k hk, eIn _ (.inr rfl) k hk, result_word hp hg hk]

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.useHint s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      NatPolyIs s'.mem (P s .r3) (result s (s.gpr .r2).toNat) := by
  refine WP.mono (wp_saving [.r4, .r5, .r6] _ (W := [pR (P s .r3)])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧ NatPolyIs s₂.mem (P s .r3) (result s (s.gpr .r2).toNat))
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.s3) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hh⟩, hm, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, hm ▸ hh⟩
  have he : encodable (BitVec.ofNat 32 g88) = true := by decide
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [gammaCmp, runBlock_cons, runStep_some, exec, Op2.eval, he, ite_true, Option.map_some]
    rfl, ?_⟩)
  have hz := VG.Proof.MlKem.Arm.cmp_z (s₁.gpr .r2) g88 (by decide)
  have hloop : ∀ g, G2 g → g = (s.gpr .r2).toNat → WP isa (mapLoop .r2 (uhBody g))
      (subFlags s₁ (s₁.gpr .r2) (BitVec.ofNat 32 g88)) fun s' =>
        (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧ Frame [pR (P s .r3)] s₁.mem s'.mem ∧
        ∀ k < 256, (coeffAt s'.mem (P s .r3) k).toNat = (result s (s.gpr .r2).toNat)[k]! := fun g hg eg => by
    subst eg
    exact loop hp hE hg hE.gpr rfl rfl rfl rfl
  refine WP.mono
    (WP.ite (decide ((s₁.gpr .r2).toNat = g88)) (by simp only [eval, subFlags, hz])
      (fun h => hloop g88 (.inr rfl) (by rw [← of_decide_eq_true h, hE.gpr]))
      (fun h => hloop g32 (.inl rfl) (by
        have := of_decide_eq_false h
        rw [hE.gpr] at this
        rcases mem_gamma2s hp.g with h' | h'
        · exact absurd h' this
        · exact h'.symm))) fun s₃ ⟨hf, _, hfr, hc⟩ =>
      ⟨hfr, hf, natPolyIs_of_toNat fun j hj => hc j (by rw [n_eq] at hj; exact hj)⟩

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

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Round.useHint (Spec.MlDsa.useHintContract Arm.abi 12) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4, .r5, .r6] _ [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_)
    (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hh⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact hh
  · sig_pub [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.useHintContract, Spec.MlDsa.useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.UseHint
