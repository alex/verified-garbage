import VerifiedGarbage.Proof.Scrypt.X86.BlockMixFun
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptBlockMix on x86 (32-bit): verified

Untrusted: everything here is checked by Lean. `SalsaSpec` of the verified
Salsa20/8 Core, from its proof by `WP.callWith`; then the `Verified` proof of
`vg_scrypt_blockmix`. Only `esp` and the arguments are public, and the taint
analysis checks that nothing else reaches an address or a branch: the words
holding `y` and `scratch` are the bases of the two writable regions, and the
code reads the pointers and `r` from the arguments, which it never writes.
The proof is written against a contract under which the code only reads its
arguments, and moved to the shared contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86

theorem salsa_nosp : NoSp Impl.Scrypt.X86.salsa := NoSp.of_all (by decide +kernel)

theorem salsa_stack : stackUse Impl.Scrypt.X86.salsa = 0 := by decide +kernel

theorem salsaSpec : SalsaSpec Impl.Scrypt.X86.salsa := by
  intro s dR d sc hdR hd hsc fd fsc hds hlo hsd hss hind hins Q hQ
  set E := s.gpr .esp with hE
  have hrs : Reg.esp ∉ [Reg.eax, dR] := by simp [Ne.symm hdR]
  have fit : 4 * [Reg.eax, dR].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, dR] s).callEntry with hsE
  have a0 : arg sE 0 = d := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hd]
  have a1 : arg sE 1 = sc := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hsc]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 8).setWidth 64 := by
    rw [hsE, callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 12 := by
    rw [hsE, callEntry_esp']; rfl
  have b8 : Region.Sub (below E 8) (below E 12) := below_sub (by omega) hlo
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below E 12) := by
    have := below_inner (sp := E) (a := 4) (b := 12) (k := 8) (by omega) hlo
    rw [show E - BitVec.ofNat 32 12 = E - BitVec.ofNat 32 8 - BitVec.ofNat 32 4 by bv_omega]
    exact this
  have e12 : 4 * [Reg.eax, dR].length + stackUse Impl.Scrypt.X86.salsa + 4 = 12 := by
    rw [salsa_stack]; rfl
  refine WP.callWith (k := Proof.Scrypt.salsaX86) salsa_correct salsa_nosp (by simp) hrs
    (by rw [e12]; exact hlo)
    (rd := [⟨argAddr sE 0, 8⟩]) (wr := [⟨d.setWidth 64, 64⟩, ⟨sc.setWidth 64, 64⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [Proof.Scrypt.salsaX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, hds, hsd.sub_left b8, hss.sub_left b8, hsd.sub_left r4, hss.sub_left r4,
      fd, fsc, ?_⟩
    rw [sub_toNat hlo]; have := E.isLt; omega
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      exact hcn
    · obtain ⟨r', hr', hc'⟩ := hind
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', by
        have : (⟨d.setWidth 64, 64⟩ : Region).Contains a n := hcn
        simp only [Region.Contains] at this hc' ⊢
        bv_omega⟩)
    · obtain ⟨r', hr', hc'⟩ := hins
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', by
        have : (⟨sc.setWidth 64, 64⟩ : Region).Contains a n := hcn
        simp only [Region.Contains] at this hc' ⊢
        bv_omega⟩)
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hind
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · obtain ⟨r', hr', hc'⟩ := hins
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
  · rw [e12] at f'
    have hsE' := callEntry_frame fit hrs
    rw [show 4 * [Reg.eax, dR].length + 4 = 12 from rfl, ← hsE] at hsE'
    rw [← hsE] at post
    simp only [Proof.Scrypt.salsaX86, arg_withRegions, State.withRegions_mem, a0, m₂] at post
    refine hQ s' rd' wr' cs' (f'.mono fun r hr => by simpa using hr) ?_
    rw [post]
    congr 1
    refine Proof.Scrypt.Memory.frame_bytesAt hsE' (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd.symm

/-! ## Constant time -/

/-- The initial taint: `esp` and the arguments are public, the words holding
`y` and `scratch` are the base addresses of the writable regions (`y` of a
length the analysis does not know), and the 12 bytes below `esp` are outside
them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 128], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 12 }

theorem wf₀ {s : State} (h : Proof.Scrypt.blockMixX86.pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have hy := hp.y_nw; have hsc := hp.s_nw; have hs := hp.sp_fit; have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.y_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_y hp.a_y
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_s hp.a_s
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rw [hp.r3] at k1; exact k1
    · exact k2

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.blockMixX86.pre s₁)
    (h₂ : Proof.Scrypt.blockMixX86.pre s₂) (hpub : Proof.Scrypt.blockMixX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [yR, scR, yA, scA, yP, sc, rr, ha 1 (by omega), ha 2 (by omega), ha 4 (by omega)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500d then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 128⟩, ⟨0x5004, 20⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem sat_pre : Proof.Scrypt.blockMixX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 1 := by decide
  have a2 : arg sat 2 = 0x2000 := by decide
  have a3 : arg sat 3 = 1 := by decide
  have a4 : arg sat 4 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x5004 := by decide
  simp only [Proof.Scrypt.blockMixX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide, trivial, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86.post s s' := by
  obtain ⟨t, s', he, h⟩ := BlockMix.correct salsaSpec (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86.pre Proof.Scrypt.blockMixX86.pub
    Impl.Scrypt.X86.blockMix :=
  VG.Taint.constantTime (A := VG.X86.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-! ## The shared contract -/

/-- `blockMixX86` with its arguments writable, as the shared contract lets them be. -/
def blockMixWide : Contract isa :=
  { Proof.Scrypt.blockMixX86 with
    pre := fun s =>
      let r := (arg s 1).toNat
      let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
      let y : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
      s.rd = [b] ∧ s.wr = [y, scratch, args] ∧
      y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧ args.Disjoint scratch ∧
      ret.Disjoint y ∧ ret.Disjoint scratch ∧ stack.Disjoint b ∧ stack.Disjoint y ∧
      stack.Disjoint scratch ∧
      (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      arg s 3 = arg s 1 ∧ 0 < r }

/-- The regions `blockMixX86` lets the code read and write. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat * 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩, ⟨(arg s 4).setWidth 64, 128⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Scrypt.blockMixX86, VG.Proof.Scrypt.X86.BlockMix.blockMixWide,
    VG.Proof.Scrypt.X86.BlockMix.narrowRd, VG.Proof.Scrypt.X86.BlockMix.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem blockMixWide_pre (s : State) (h : blockMixWide.pre s) :
    Proof.Scrypt.blockMixX86.pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩

/-- A state satisfying `blockMixWide.pre`. -/
def wideSat : State :=
  { sat with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩, ⟨0x5004, 20⟩] }

theorem blockMixWide_implies :
    blockMixWide.Implies (Spec.Scrypt.blockMixContract X86.abi 12) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 1 := by decide
  have a2 : arg wideSat 2 = 0x2000 := by decide
  have a3 : arg wideSat 3 = 1 := by decide
  have a4 : arg wideSat 4 = 0x3000 := by decide
  have e : argAddr wideSat 0 = 0x5004 := by decide
  have esp : wideSat.gpr .esp = 0x5000 := rfl
  sig_implies [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig, blockMixWide,
    Proof.Scrypt.blockMixX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp] using wideSat

/-- The proof is written against `blockMixX86`, widened to writable arguments. -/
theorem blockMix_verified :
    Verified X86.target Impl.Scrypt.X86.blockMix (Spec.Scrypt.blockMixContract X86.abi 12) :=
  have hsat := blockMixWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct blockMix_correct blockMix_ct (.refl ⟨sat, sat_pre⟩))
    narrowRd narrowWr blockMixWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies blockMixWide_implies

end VG.Proof.Scrypt.X86.BlockMix
