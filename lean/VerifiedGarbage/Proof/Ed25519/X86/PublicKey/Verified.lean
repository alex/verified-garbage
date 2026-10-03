import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.CTReady
import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Layout
import VerifiedGarbage.Proof.Framework.Contract

/-! Merged from `Proof.Ed25519.X86.PublicKey.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86.PublicKey.CTCommon`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value setup)

def Two (s₁ s₂ : State) (P : State → State → Prop) (a b : State) : Prop :=
  Ctx s₁ a ∧ Ctx s₂ b ∧ P s₁ a ∧ P s₂ b

variable {s₁ s₂ : State}

theorem esp_eq (pub : pkLocal.pub s₁ s₂) : esp s₁ = esp s₂ := congrArg (· - BitVec.ofNat 32 256) pub.1

theorem argValue_eq (pub : pkLocal.pub s₁ s₂) {v : Value} (hv : Whole.valid 3 v) : argValue s₁ v = argValue s₂ v := by
  cases v with
  | const _ => rfl
  | frame d => exact congrArg (· + BitVec.ofNat 32 d) (esp_eq pub)
  | caller i d =>
    apply congrArg (· + BitVec.ofNat 32 d)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by change i < 3 at hv; omega) with rfl | rfl | rfl
    · exact pub.2.1
    · exact pub.2.2.1
    · exact pub.2.2.2

theorem two_esp (pub : pkLocal.pub s₁ s₂) {P : State → State → Prop} {a b : State} (h : Two s₁ s₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.esp.trans ((esp_eq pub).trans h.2.1.esp.symm)

theorem two_wp (h₁ : Facts s₁) (h₂ : Facts s₂) {P Q : State → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two s₁ s₂ P) c fun _ _ => True)
    (hw : ∀ s t, Facts s → Ctx s t → P s t → WP isa c t fun u => Ctx s u ∧ Q s u) :
    RelCT isa (Two s₁ s₂ P) c (Two s₁ s₂ Q) :=
  (hct.wp fun a b h => ⟨hw s₁ a h₁ h.1 h.2.2.1, hw s₂ b h₂ h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) (vs : List Value) (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (setup 0 vs)) hint).isSome = true) :
    RelCT isa (Two s₁ s₂ fun _ _ => True) (.block (setup 0 vs)) (Two s₁ s₂ (Slots vs)) :=
  two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) ht) fun _ _ h hc _ =>
    WP.mono (setup_ok h hc hn hv) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem call_args_eq (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {a b : State} (h : Two s₁ s₂ (Slots vs) a b) {j : Nat} (hj : j < vs.length) :
    arg a.callEntry j = arg b.callEntry j := by
  rw [Whole.call_arg h.1.esp h₁.toBounds.call (by have := h₁.toBounds.frame; omega) (by omega),
    Whole.call_arg h.2.1.esp h₂.toBounds.call (by have := h₂.toBounds.frame; omega) (by omega),
    h.2.2.1 j hj, h.2.2.2 j hj]
  exact argValue_eq pub (hv _ (List.getElem_mem hj))

theorem call_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v)
    {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (sp : NoSp c) (stack : stackUse c ≤ 20)
    (ready : ∀ {s t : State}, Facts s → Ctx s t → Slots vs s t →
      Whole.CallReady k (esp s) (pkRd s) (pkWr s) t)
    (kp : ∀ (a b : State) ar aw br bw, a.gpr .esp = b.gpr .esp →
      (∀ j < vs.length, arg a.callEntry j = arg b.callEntry j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two s₁ s₂ (Slots vs)) (.call name c) (Two s₁ s₂ fun _ _ => True) := by
  apply two_wp h₁ h₂
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h₁ h.1 h.2.2.1
    let rb := ready h₂ h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (two_esp pub h) (fun _ hj => call_args_eq h₁ h₂ pub hn hv h hj),
      ca, wa, cb, wb, two_esp pub h⟩
  · intro s t h hc hs
    exact WP.mono ((ready h hc hs).wp hc correct sp stack h.toBounds.call) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

variable {s₁ s₂ : State}

theorem init_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots initValues))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : initValues.length ≤ 6) (by simp [initValues, Whole.valid])
    (Proof.Sha512.X86.Stream.init_verified _).1 (Proof.Sha512.X86.Stream.init_verified _).2.1
    Whole.init_nosp (by rw [Whole.init_stack]; decide) init_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj 0 (by decide)⟩

theorem update_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots updateValues)) (.call Spec.Sha512.updateApi.name Impl.Sha512.X86.Stream.update)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : updateValues.length ≤ 6) (by simp [updateValues, Whole.valid])
    Proof.Sha512.X86.Stream.Update.update_verified.1 Proof.Sha512.X86.Stream.Update.update_verified.2.1
    Whole.update_nosp (by rw [Whole.update_stack]) update_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj⟩

theorem finalize_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots finalizeValues)) (.call Spec.Sha512.finalizeApi.name Impl.Sha512.X86.Stream.finalize)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : finalizeValues.length ≤ 6) (by simp [finalizeValues, Whole.valid])
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.1 Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1
    Whole.finalize_nosp (by rw [Whole.finalize_stack]) finalize_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj⟩

theorem base_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) :
    RelCT isa (Two s₁ s₂ (Slots baseValues)) (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two s₁ s₂ fun _ _ => True) := by
  apply call_ct h₁ h₂ pub (by decide : baseValues.length ≤ 6) (by simp [baseValues, Whole.valid])
    scalarBase_ok scalarBase_ct base_nosp (by rw [base_stack]; decide) base_ready
  intro a b ar aw br bw he hj
  exact ⟨congrArg (· - 4) he, hj 0 (by decide), hj 1 (by decide), hj 2 (by decide)⟩

theorem prune_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) (.block prune) (Two s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (prune_step h hc (digest := Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64) rfl)
    fun _ hu => ⟨hu.1, trivial⟩

theorem wipe_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) (.block wipe) (Two s₁ s₂ fun _ _ => True) := by
  refine two_wp h₁ h₂ (Whole.block_rel (fun _ _ h => two_esp pub h) (by taint_decide)) ?_
  intro s t h hc _
  exact WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun _ hu => ⟨hu.1, trivial⟩

theorem body_ct (h₁ : Facts s₁) (h₂ : Facts s₂) (pub : pkLocal.pub s₁ s₂) : RelCT isa (Two s₁ s₂ fun _ _ => True) body (Two s₁ s₂ fun _ _ => True) := by
  have i := setup_ct h₁ h₂ pub initValues (by decide) (by simp [initValues, Whole.valid]) (by taint_decide)
  have u := setup_ct h₁ h₂ pub updateValues (by decide) (by simp [updateValues, Whole.valid]) (by taint_decide)
  have f := setup_ct h₁ h₂ pub finalizeValues (by decide) (by simp [finalizeValues, Whole.valid]) (by taint_decide)
  have b := setup_ct h₁ h₂ pub baseValues (by decide) (by simp [baseValues, Whole.valid]) (by taint_decide)
  exact ((i.seq (init_ct h₁ h₂ pub)).seq
    ((u.seq (update_ct h₁ h₂ pub)).seq (f.seq (finalize_ct h₁ h₂ pub)))).seq
    ((prune_ct h₁ h₂ pub).seq ((b.seq (base_ct h₁ h₂ pub)).seq (wipe_ct h₁ h₂ pub)))

theorem publicKey_ct : ConstantTime isa pkLocal.pre pkLocal.pub publicKey := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  exact ⟨(body_ct (facts p₁) (facts p₂) hp _ _ _ _ _ _
    ⟨push_ctx p₁, push_ctx p₂, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.PublicKey
materialize_code publicKey
end VG.Impl.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Contract`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86

def pkWide : Contract isa := { pkLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def pkSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pkSatMem
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem pkWide_pre (s : State) (h : pkWide.pre s) :
    pkLocal.pre (s.withRegions (pkRd s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩ := h
  simp only [pkLocal, pkRd, pkWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩

theorem pkWide_implies : pkWide.Implies (Spec.Ed25519.publicKeyContract X86.abi 280) := by
  have a0 : arg pkSatState 0 = 0x1000 := by decide
  have a1 : arg pkSatState 1 = 0x2000 := by decide
  have a2 : arg pkSatState 2 = 0x4000 := by decide
  have e : argAddr pkSatState 0 = 0x8004 := by decide
  have sp : pkSatState.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, pkWide, pkLocal, below, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, e, sp] using pkSatState

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem publicKey_verified : Verified X86.target publicKey (Spec.Ed25519.publicKeyContract X86.abi 280) := by
  have hsat := pkWide_implies.sat_left
  have satLocal : ∃ s, pkLocal.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target publicKey pkLocal :=
    Verified.of_correct (fun _ h => publicKey_ok h) publicKey_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal pkRd pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86.PublicKey
