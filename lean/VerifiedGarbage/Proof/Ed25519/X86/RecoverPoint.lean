import VerifiedGarbage.Proof.Ed25519.X86.RecoverSign
import VerifiedGarbage.Proof.Ed25519.X86.RecoverCandidate
import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep

/-! Candidate validation implements RFC 8032's recoverX exactly. -/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) (x y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa recoverSign s fun t => FieldKeep base s t ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hs b hb) fun t ⟨kt, tr⟩ => ?_
  exact ⟨kt, by rw [hx, hy] at tr; exact tr⟩

theorem recoverChecks_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : s.gpr .esi = signWord b) (y : Spec.X25519.Fe)
    (hx : env s.mem base 0 = rootX y) (hy : env s.mem base 1 = y)
    (hu : env s.mem base 6 = rootU y)
    (hvx : env s.mem base 11 = rootV y * rootX y * rootX y)
    (hnu : env s.mem base 12 = 0 - rootU y) :
    WP isa recoverChecks s fun t => FieldKeep base s t ∧ DecodeResult base (recoverResult y b) t := by
  refine WP.seq (WP.mono (fieldEqual_ok hs 11 6) fun c ⟨kc, ce, cz⟩ => ?_)
  have cx : env c.mem base 0 = rootX y := (ce 0 (by decide)).trans hx
  have cy : env c.mem base 1 = y := (ce 1 (by decide)).trans hy
  apply WP.ite (decide (rootV y * rootX y * rootX y = rootU y)) (by rw [← hvx, ← hu]; exact cz)
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kc.ctx hs) b (kc.keep.esi.trans hb) _ _ cx cy) fun t ⟨kt, tr⟩ => ?_
    exact ⟨kc.trans kt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kc.ctx hs) 11 12) fun d ⟨kd, de, dz⟩ => ?_)
    have kcd := kc.trans kd
    have dx : env d.mem base 0 = rootX y := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = y := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV y * rootX y * rootX y = 0 - rootU y))
      (by rw [ce 11 (by decide), ce 12 (by decide), hvx, hnu] at dz; exact dz)
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] (kcd.ctx hs))
        fun e ⟨ke, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX y * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = y := by rw [ve]; exact dy
      have kcde := kcd.trans ke
      refine WP.mono (sign_known (kcde.ctx hs) b (kcde.keep.esi.trans hb) _ _ ex ey)
        fun t ⟨kt, tr⟩ => ?_
      exact ⟨kcde.trans kt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tr⟩ => ?_
      exact ⟨kcd.trans kt, by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

theorem recoverPoint_ok {s : State} {base : BitVec 32} (hs : Ctx base s)
    (b : Bool) (hb : wd s.mem base 32 = signWord b) :
    WP isa recoverPoint s fun t => IKeep base s t ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec]
  refine WP.seq (WP.mono (recoverCandidate_ok hs) fun a ⟨ka, ax, ay, _, au, _, avx, anu⟩ => ?_)
  have ca := ka.ctx hs
  refine WP.seq (Wp.wp_ldm ca.edi (ca.inRW (by decide) (by decide)) fun c hc => WP.block_nil ?_)
  have kc : IKeep base a c := IKeep.of_counter hc
  have cb : c.gpr .esi = signWord b := by
    rw [hc.gpr]
    change wd a.mem base 32 = _
    rw [IKeep.word ka hs 32 (by decide), hb]
  refine WP.mono (recoverChecks_ok (kc.ctx ca) b cb (env s.mem base 1)
    (by rw [hc.mem]; exact ax) (by rw [hc.mem]; exact ay) (by rw [hc.mem]; exact au)
    (by rw [hc.mem]; exact avx) (by rw [hc.mem]; exact anu)) fun t ⟨kt, tr⟩ => ?_
  exact ⟨(ka.trans kc).trans (IKeep.of_field kt), tr⟩

end VG.Proof.Ed25519.X86
