import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Hash
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def challenge (L : Lay) : Region := ⟨(L.E + 128).setWidth 64, 64⟩
def equationRd (L : Lay) : List Region := [L.PK, L.SIG, challenge L, ⟨L.E.setWidth 64, 16⟩]
def equationWr (L : Lay) : List Region := [⟨L.scr.setWidth 64, 0⟩, L.SCR]
def EqArgs (L : Lay) (s : State) : Prop := Whole.slots L.E s 0 = L.pk ∧
  Whole.slots L.E s 1 = L.sig ∧ Whole.slots L.E s 2 = L.E + 128 ∧ Whole.slots L.E s 3 = L.scr

theorem equation_nosp : NoSp verifyEquation := NoSp.of_all (by lit_decide)
theorem equation_stack : stackUse verifyEquation = 0 := by lit_decide

theorem challengeWithin (hL : L.Ok) : Whole.Within (challenge L) L.FR :=
  ⟨128, Whole.frame_addr (hashSpace hL).frameFit (by decide), by change 128 + 64 ≤ 256; decide⟩

theorem equation_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (equationRd L) (equationWr L)) := by
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  obtain ⟨a0, a1, a2, a3⟩ := ha
  have e0 := (ca (j := 0) (by decide)).trans a0
  have e1 := (ca (j := 1) (by decide)).trans a1
  have e2 := (ca (j := 2) (by decide)).trans a2
  have e3 := (ca (j := 3) (by decide)).trans a3
  have ab := Whole.arg_base hc.esp (equationRd L) (equationWr L)
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, e0, e1, e2, e3, ab,
    sub, addr_zero, scR]
  refine ⟨rfl, rfl, hL.sc _ (by simp [Lay.inputs]), hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((challengeWithin hL).sub p hp)),
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)),
    hL.kc.sub_left (Whole.below_sub_stack hL.below (by decide)), hL.np, hL.ns,
    Whole.frame_fit H.frameFit (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256), hL.nc, ?_⟩
  have e : (L.E - 4).toNat = L.E.toNat - 4 := sub_toNat (k := 4) (by have := hL.below; omega)
  rw [e]
  have := hL.top; omega

theorem equation_correct_result (s : State) (h : verifyLocal.pre s) :
    ∃ tr t, Exec isa verifyEquation s tr t ∧ abiPreserved s t ∧ verifyLocal.post s t := verify_correct h

theorem equation_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => Ctx L g m₀ t ∧
      t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 64)
        (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64)) := by
  have H := hashSpace hL
  have wz : Whole.Within ⟨L.scr.setWidth 64, 0⟩ L.SCR := ⟨0, by simp, by change 0 ≤ 8192; decide⟩
  have wsc : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩
  have cov : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply hash_covers
    simp only [equationRd, equationWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, by simp, by simp⟩
    · exact .inl (challengeWithin hL)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered wz
    · exact scratch_covered wsc
  have ws : ∀ r ∈ equationWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
    hash_writes (by
      simp only [equationWr, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact .inr wz
      · exact .inr wsc)
  with_reducible
    refine Whole.call_ok hc hL.below equation_correct_result equation_nosp (by rw [equation_stack]; decide)
      (equation_pre hc hL ha) cov ws fun t ht _ _ post => ⟨ht, ?_⟩
  obtain ⟨t₂, hm, hg, hp⟩ := post
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  obtain ⟨a0, a1, a2, _⟩ := ha
  change t₂.gpr .eax = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 0).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 64)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 2).setWidth 64) 64)) at hp
  rw [hg .eax (by decide), (ca (j := 0) (by decide)).trans a0,
    (ca (j := 1) (by decide)).trans a1, (ca (j := 2) (by decide)).trans a2] at hp
  have pk : Spec.Ed25519.bytesAt s.callEntry.mem (L.pk.setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem (L.pk.setWidth 64) 32 := by
    apply Whole.callEntry_bytes (r := L.PK) ?_ (by change 32 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact ((hL.ks _ (by simp [Lay.inputs])).sub_left (Whole.below_sub_stack hL.below (by decide))).symm
  have sg : Spec.Ed25519.bytesAt s.callEntry.mem (L.sig.setWidth 64) 64 =
      Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 64 := by
    apply Whole.callEntry_bytes (r := L.SIG) ?_ (by change 64 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact ((hL.ks _ (by simp [Lay.inputs])).sub_left (Whole.below_sub_stack hL.below (by decide))).symm
  have ch : Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 =
      Spec.Ed25519.bytesAt s.mem ((L.E + 128).setWidth 64) 64 := by
    apply Whole.callEntry_bytes (r := challenge L) ?_ (by change 64 ≤ 2 ^ 64; decide)
    rw [hc.esp]
    exact (Whole.frame_below hL.below H.frameFit (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256)).symm
  have ce : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  rw [pk, sg, ch, ce] at hp
  exact hp

end VG.Proof.Ed25519.X86.VerifyMessage
