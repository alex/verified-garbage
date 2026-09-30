import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttLoop
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt`

Untrusted: everything here is checked by Lean. The table stored and `q`
loaded (`pro_ok`); each layer is `nttLayer` (`lay_ok` with `bfly_spec`),
and the eight layers are `NTT` (`ntt_eq_layers`), all in the frames that
save `r4`–`r10` (`wp_saving`). `LI`, `pro_ok`, `PreE` and `pre_entry` serve
`NTT⁻¹` too.
-/

namespace VG.Proof.MlDsa.Arm.Arith.Ntt

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

section
variable (s : State)

abbrev pf : BitVec 32 := s.gpr .r0
abbrev ps : BitVec 32 := s.gpr .r1
abbrev F : Addr := State.addr (pf s)
abbrev S : Addr := State.addr (ps s)

end

/-- The precondition of both transforms, on entry. -/
structure PreE (s : State) : Prop where
  sp : 28 ≤ s.sp.toNat
  rd : s.rd = []
  wr : s.wr = [polyRegion (F s), polyRegion (S s)]
  fs : (polyRegion (F s)).Disjoint (polyRegion (S s))
  sF : (belowA s.sp 28).Disjoint (polyRegion (F s))
  sS : (belowA s.sp 28).Disjoint (polyRegion (S s))
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (F s)

/-- What the transforms need of the state after the pushes. -/
structure PreB (s : State) : Prop where
  wF : polyRegion (F s) ∈ s.wr
  wS : polyRegion (S s) ∈ s.wr
  fs : (polyRegion (F s)).Disjoint (polyRegion (S s))
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (F s)

theorem pre_entry {s s₁ : State} (hp : PreE s) (hE : Entry 28 s s₁) :
    PreB s₁ ∧ polyAt s₁.mem (F s₁) = polyAt s.mem (F s) ∧ F s₁ = F s ∧ S s₁ = S s := by
  have g := hE.gpr
  have eF : F s₁ = F s := by simp only [F, pf, g]
  have eS : S s₁ = S s := by simp only [S, ps, g]
  have dF : ∀ r ∈ [belowA s.sp 28], (polyRegion (F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame hE.frame dF, eF, eS⟩
  · rw [eF]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eS]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eF, eS]; exact hp.fs
  · simp only [pf, g]; exact hp.fitF
  · simp only [ps, g]; exact hp.fitS
  · rw [eF]; exact reduced_frame hE.frame dF hp.red

/-- Between layers: the polynomial `G` at `f`, the table `tab` at `scratch`,
and entry `k` of the table at `r1`, from the state `s₁` after the pushes. -/
structure LI (tab : Nat → Nat) (s₁ : State) (G : Poly) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₁
  r1 : s.gpr .r1 = ps s₁ + BitVec.ofNat 32 (4 * k)
  r4 : s.gpr .r4 = Qw
  poly : PolyIs s.mem (F s₁) G
  tab : Tab tab s.mem (S s₁)
  frame : Frame [polyRegion (F s₁), polyRegion (S s₁)] s₁.mem s.mem
  keep : Keep [.r11, .lr] s₁ s

theorem LI.step {tab : Nat → Nat} {s₁ : State} {G G' : Poly} {k k' : Nat} {s s' : State}
    (hI : LI tab s₁ G k s) (hP : PolyIs s'.mem (F s₁) G') (hf : Frame [polyRegion (F s₁)] s.mem s'.mem)
    (h0 : s'.gpr .r0 = pf s₁) (h1 : s'.gpr .r1 = ps s₁ + BitVec.ofNat 32 (4 * k'))
    (hk : Keep [.r4, .r11, .lr] s s') (hd : (polyRegion (S s₁)).Disjoint (polyRegion (F s₁))) :
    LI tab s₁ G' k' s' :=
  ⟨h0, h1, (hk.gpr .r4 (by decide)).trans hI.r4, hP,
    hI.tab.frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd),
    hI.frame.trans (hf.mono (by simp)), hI.keep.trans (hk.mono (by decide))⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ Chain (256 / len) ls

theorem lens_fwd : ∀ len ∈ nttLens, 128 / len + 128 / len = 256 / len ∧ 256 / len ≤ 256 := by decide

theorem zetaTab_of : TabOf zetaTab zetas := fun k _ => zetaNat_eq k

theorem zetaTab_lt : ∀ k < 256, zetaTab k < q := fun k _ => zetaNat_lt k

theorem lays_ok {s₁ : State} (hp : PreB s₁) :
    ∀ (ls : List Nat) (G : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttLens) → Chain k ls →
      LI zetaTab s₁ G k s →
      WP isa (nttLays ls) s fun s' => ∃ k', LI zetaTab s₁ (ls.foldl nttLayer G) k' s'
  | [], G, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := lens_fwd len hlen
    refine WP.seq (WP.mono (lay_ok bfly_spec zetaTab_of hp.fitF hp.fitS hlen .add (.inl rfl)
      (fun c => 128 / len + c) (fun c hc => by omega)
      (fun c _ => by
        simp only [nextZ, ite_true, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
          ← BitVec.ofNat_add]
        congr 2)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    exact lays_ok hp ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1', ← h1]) hk' hp.fs.symm)

/-- The table `tab` to `scratch`, `q` to `r4`, and `r1` at entry `k`. -/
theorem pro_ok {s : State} (hp : PreB s) (tab : Nat → Nat) (ht : ∀ k < 256, tab k < q) (d : BitVec 32) (k : Nat)
    (hd : BitVec.ofNat 32 (4 * k) = d) (he : encodable d = true) :
    WP isa (.block (storeTab tab 256 ++ loadQ .r4 ++ [.dp .add .r1 .r1 (.imm d)])) s
      (LI tab s (polyAt s.mem (F s)) k) := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeTab_ok tab ht s (zB := ps s) rfl hp.fitS hp.wS) fun s₁ ⟨ht₁, hf₁, k₁⟩ => ?_
  have e1 : s₁.gpr .r1 = ps s := k₁.gpr .r1 (by decide)
  have e0 : s₁.gpr .r0 = pf s := k₁.gpr .r0 (by decide)
  run_block [loadQ, e0, e1, he, loadQ_val]
  refine ⟨by simp [e0], by simp [hd], by simp, ?_, ht₁, hf₁.mono (by simp), ?_⟩
  · exact polyIs_frame hf₁ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs) ⟨hp.red, rfl⟩
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [k₁.gpr _ (by decide : Reg.r11 ∈ _), k₁.gpr _ (by decide : Reg.lr ∈ _)],
      k₁.rd, k₁.wr, k₁.sp⟩

theorem chain_fwd : Chain 1 nttLens := by simp only [nttLens, Chain]; decide

theorem pre_of {s : State} (h : (Spec.MlDsa.nttContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The frames' region is disjoint from the buffers. -/
theorem stack_disj {s : State} (hp : PreE s) :
    ∀ R ∈ [polyRegion (F s), polyRegion (S s)], (belowA s.sp (4 * nttSaved.length)).Disjoint R := by
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [hp.sF, hp.sS]

/-- The callee-saved registers, from those `saving nttSaved` restores. -/
theorem preserved_of {s s' s₂ : State}
    (hg : ∀ r, s'.gpr r = if r ∈ nttSaved then s.gpr r else s₂.gpr r)
    (h11 : s₂.gpr .r11 = s.gpr .r11) (hlr : s₂.gpr .lr = s.gpr .lr) : ∀ r ∈ preserved, s'.gpr r = s.gpr r :=
  preserved_of_saving hg fun r hr hn => by
    simp only [preserved, nttSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    exacts [h11, hlr]

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.ntt s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.ntt (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.ntt (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB zetaTab zetaTab_lt 4 1 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.mono (lays_ok hpB nttLens _ 1 s₂ (fun _ h => h) chain_fwd hI) fun s₃ ⟨k, hI'⟩ => ?_
  refine ⟨by rw [← eF, ← eS]; exact hI'.frame, ?_, ?_, ?_⟩
  · rw [hI'.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [hI'.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · rw [← eP, ← eF, VG.Proof.MlDsa.Arith.ntt_eq_layers]; exact hI'.poly

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.ntt (Spec.MlDsa.nttContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Ntt
