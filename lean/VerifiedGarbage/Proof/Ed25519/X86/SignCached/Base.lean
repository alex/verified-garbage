import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (scalarBase)
open VG.Impl.Ed25519.X86.PublicKey (callWith)

def baseRd (L : Lay) : List Region := [field L 96, ⟨L.E.setWidth 64, 12⟩]
def baseOut (L : Lay) : Region := ⟨L.out.setWidth 64, 32⟩
def baseWr (L : Lay) : List Region := [baseOut L, L.SCR]
def BaseArgs (L : Lay) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.out ∧ Whole.slots L.E t 1 = fp L 96 ∧ Whole.slots L.E t 2 = L.scr

theorem base_nosp : NoSp scalarBase := NoSp.of_all (by lit_decide)
theorem base_stack : stackUse scalarBase = 0 := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem base_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s) :
    scalarBaseLocal.pre (s.callEntry.withRegions (baseRd L) (baseWr L)) := by
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  have a0 := (ca (j := 0) (by decide)).trans ha.1
  have a1 := (ca (j := 1) (by decide)).trans ha.2.1
  have a2 := (ca (j := 2) (by decide)).trans ha.2.2
  have ae := Whole.arg_base hc.esp (baseRd L) (baseWr L)
  have ret : Region.Sub ⟨(L.E - 4).setWidth 64, 4⟩ L.STK := Whole.below_sub_stack H.below (by decide)
  have args : Region.Sub ⟨L.E.setWidth 64, 12⟩ L.STK :=
    fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)
  have out : Region.Sub (baseOut L) L.OUT := Region.sub_prefix (by decide)
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, ae]
  refine ⟨rfl, rfl, hL.oc.sub_left out, hL.kc.sub_left (field_sub hL (by decide)),
    (hL.ko.sub_left args).sub_right out, hL.kc.sub_left args,
    (hL.ko.sub_left ret).sub_right out, hL.kc.sub_left ret,
    by have := hL.no; omega, field_fit hL (by decide), hL.nc, ?_⟩
  change (L.E - BitVec.ofNat 32 4).toNat + 16 ≤ 2 ^ 32
  rw [sub_toNat (k := 4) (by have := hL.below; omega)]
  have := hL.top; omega

theorem base_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : BaseArgs L s) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g m₀ t ∧
      Frame (baseWr L ++ [below L.E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32) := by
  have cov := hash_covers (L := L) (rs := baseRd L ++ baseWr L) (by
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], 0, by simp [baseOut], by change 0 + 32 ≤ 64; decide⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc hL.below scalarBase_ok base_nosp (by rw [base_stack]; decide)
      (base_pre hc hL ha) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨s₂, hm, _, hp⟩ := post
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt s₂.mem ((arg s.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 32) at hp
  rw [hm, (ca (by decide)).trans ha.1, (ca (by decide)).trans ha.2.1] at hp
  rw [hp, field_ce hc hL (by decide)]

theorem base_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (baseOut L)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.caller 0 0, .frame 96, .caller 5 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.out + 0#32 at a0
  change Whole.slots L.E u 2 = L.scr + 0#32 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hft, hp⟩ =>
    ⟨ht, primitive_frame hf hft, ?_⟩
  rw [hp, field_setup hL hf (by decide) (by decide)]

end VG.Proof.Ed25519.X86.SignCached
