import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified

/-!
# ML-DSA on x86-64, `sign_message`: the signing functions on `μ` it calls

Untrusted: everything here is checked by Lean. `vg_mldsa*_sign`, with any
implementation `v` of the polynomial arithmetic, is a function
`sign_message` can call (`signFn`): its proofs give its contract, it never
writes `rsp`, and its calls nest at most four deep, which, as whether it
writes `rsp`, is checked on the code with the arithmetic's functions empty
(`Same`), given that theirs nest at most three deep.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl Code.allInstrs_of_all)
open VG.Proof.MlDsa.X86_64.Sign (primsWith prims_okWith sign_correct sign_ct sign_ctl sign_same Ok3)
open VG.Spec.MlDsa

/-- Calls nesting at most `n + 1` deep, from functions whose calls nest at most `n` deep. -/
theorem depthCompN (n : Nat) : Comp (fun c => decide (c.depth ≤ n + 1)) (fun c => decide (c.depth ≤ n)) := by
  refine ⟨fun a b => ?_, fun _ t e => ?_, fun _ _ => rfl, fun _ b => ?_, rfl⟩
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth]
    exact decide_eq_decide.mpr (by omega)

/-- `NoSp` from evaluating the code. -/
abbrev noSpB (c : Prog isa) : Bool := c.allInstrs fun i => !Taint.clobbers i .rsp

theorem noSp_of {c : Prog isa} (h : noSpB c = true) : NoSp c := Proof.MlKem.X86_64.nosp_of h

theorem noSpB_of {c : Prog isa} (h : NoSp c) : noSpB c = true := by
  rw [noSpB, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem ok3_of {p : Params} (hp : p ∈ params) : Ok3 p := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact hp

theorem sign0_noSp {p : Params} (h3 : Ok3 p) :
    noSpB (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem sign0_depth {p : Params} (h3 : Ok3 p) :
    decide ((Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) p).depth ≤ 4) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

/-- `vg_mldsa*_sign`, with the polynomial arithmetic of `v`. -/
theorem signFn (v : ArithImpl) {p : Params} (hp : p ∈ params) :
    SignFn p (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) p) := by
  have h3 := ok3_of hp
  have dep : ∀ {c : Prog isa}, c.depth ≤ 3 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true h
  have dep2 : ∀ {c : Prog isa}, c.depth ≤ 2 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true (by omega)
  refine ⟨sign_correct (prims_okWith v) h3 (Proof.MlDsa.X86_64.Sign.sign_ctl v h3), sign_ct (prims_okWith v) h3,
    noSp_of (Same.ok (sign_same (Comp.all _) (noSpB_of v.ok.ntt.nosp) (noSpB_of v.ok.invNtt.nosp)
      (noSpB_of v.ok.mul.nosp) (noSpB_of v.ok.mulAdd.nosp) (noSpB_of v.ok.add.nosp) (noSpB_of v.ok.sub.nosp)
      (noSpB_of v.ok.rej4.nosp) (noSpB_of v.ok.expandMask4.nosp) (noSpB_of v.ok.highBits.nosp)
      (noSpB_of v.ok.lowBits.nosp) (noSpB_of v.ok.normLt.nosp) (noSpB_of v.ok.makeHint.nosp) p) (sign0_noSp h3)),
    of_decide_eq_true (Same.ok (sign_same (depthCompN 3) (dep2 v.ok.ntt.depth) (dep2 v.ok.invNtt.depth)
      (dep2 v.ok.mul.depth) (dep2 v.ok.mulAdd.depth) (dep2 v.ok.add.depth) (dep2 v.ok.sub.depth)
      (dep v.ok.rej4.depth) (dep v.ok.expandMask4.depth) (dep2 v.ok.highBits.depth) (dep2 v.ok.lowBits.depth)
      (dep2 v.ok.normLt.depth) (dep2 v.ok.makeHint.depth) p) (sign0_depth h3))⟩

theorem kabs_spSafe : Impl.Sha3.X86_64.Stream.absorb.all (fun i => !isa.writesSp i) = true := by decide +kernel
theorem kpad_spSafe : Impl.Sha3.X86_64.Stream.pad.all (fun i => !isa.writesSp i) = true := by decide +kernel
theorem ksqz_spSafe : Impl.Sha3.X86_64.Stream.squeeze.all (fun i => !isa.writesSp i) = true := by decide +kernel

theorem arg_wsp (d : Reg) (hd : d ∈ argRegs6) (a : Arg) : (a.mov d).all (fun i => !isa.writesSp i) = true := by
  have : d ≠ .rsp := fun e => by subst e; revert hd; decide
  cases a <;> cases d <;> simp_all [Arg.mov, Instr.dst]

theorem setArgs_wsp (as : List Arg) : (setArgs as).all (fun i => !isa.writesSp i) = true := by
  rw [List.all_eq_true]
  intro i hi
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  exact List.all_eq_true.mp (arg_wsp d (List.of_mem_zip hm).1 a) i hi

theorem signMessage_spSafe {p : Params} {n : String} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.MlDsa.X86_64.Message.signMessage n c p).all (fun i => !isa.writesSp i) = true := by
  generalize hq : (fun i => !isa.writesSp i) = q at hc ⊢
  have ha : Impl.Sha3.X86_64.Stream.absorb.all q = true := hq ▸ kabs_spSafe
  have hp' : Impl.Sha3.X86_64.Stream.pad.all q = true := hq ▸ kpad_spSafe
  have hs : Impl.Sha3.X86_64.Stream.squeeze.all q = true := hq ▸ ksqz_spSafe
  have hsa : ∀ as, (setArgs as).all q = true := fun as => hq ▸ setArgs_wsp as
  have hmv : ∀ a, (Arg.mov .rdi a).all q = true := fun a => hq ▸ arg_wsp .rdi (by decide) a
  simp only [Impl.MlDsa.X86_64.Message.signMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.zeroSt, Impl.MlDsa.X86_64.Message.kabs,
    Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz, Impl.MlDsa.X86_64.Message.callA, Code.all,
    hc, ha, hp', hs, hsa, hmv, Bool.and_true, Bool.true_and]
  subst hq
  decide

end VG.Proof.MlDsa.X86_64.Message
