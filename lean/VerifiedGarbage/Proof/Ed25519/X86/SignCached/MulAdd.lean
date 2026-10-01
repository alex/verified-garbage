import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (scalarMulAdd)
open VG.Impl.Ed25519.X86.PublicKey (callWith)

def half (L : Lay) : Region := ⟨(L.out + 32).setWidth 64, 32⟩
def mulRd (L : Lay) : List Region := [field L 96, field L 128, field L 32, ⟨L.E.setWidth 64, 20⟩]
def mulWr (L : Lay) : List Region := [half L, L.SCR]
def MulArgs (L : Lay) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.out + 32 ∧ Whole.slots L.E t 1 = fp L 96 ∧
    Whole.slots L.E t 2 = fp L 128 ∧ Whole.slots L.E t 3 = fp L 32 ∧ Whole.slots L.E t 4 = L.scr

theorem mul_nosp : NoSp scalarMulAdd := NoSp.of_all (by lit_decide)
theorem mul_stack : stackUse scalarMulAdd = 0 := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem half_addr (hL : L.Ok) : (L.out + 32).setWidth 64 = L.out.setWidth 64 + 32 :=
  addr_eq (x := L.out) (k := 32) (by have := hL.no; omega)

theorem halfWithin (hL : L.Ok) : Whole.Within (half L) L.OUT :=
  ⟨32, half_addr hL, by change 32 + 32 ≤ 64; decide⟩

theorem mul_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (mulRd L) (mulWr L)) := by
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  have a0 := (ca (j := 0) (by decide)).trans ha.1
  have a1 := (ca (j := 1) (by decide)).trans ha.2.1
  have a2 := (ca (j := 2) (by decide)).trans ha.2.2.1
  have a3 := (ca (j := 3) (by decide)).trans ha.2.2.2.1
  have a4 := (ca (j := 4) (by decide)).trans ha.2.2.2.2
  have ae := Whole.arg_base hc.esp (mulRd L) (mulWr L)
  have ret : Region.Sub ⟨(L.E - 4).setWidth 64, 4⟩ L.STK := Whole.below_sub_stack H.below (by decide)
  have args : Region.Sub ⟨L.E.setWidth 64, 20⟩ L.STK :=
    fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)
  have out := (halfWithin hL).sub
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, a3, a4, ae]
  refine ⟨rfl, rfl, hL.oc.sub_left out, hL.kc.sub_left (field_sub hL (d := 96) (by decide)),
    hL.kc.sub_left (field_sub hL (d := 128) (by decide)), hL.kc.sub_left (field_sub hL (d := 32) (by decide)),
    (hL.ko.sub_left args).sub_right out, hL.kc.sub_left args,
    (hL.ko.sub_left ret).sub_right out, hL.kc.sub_left ret, ?_,
    field_fit hL (by decide), field_fit hL (by decide), field_fit hL (by decide), hL.nc, ?_⟩
  · have h := hL.no
    rw [BitVec.toNat_add, show (32 : BitVec 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  · change (L.E - BitVec.ofNat 32 4).toNat + 24 ≤ 2 ^ 32
    rw [sub_toNat (k := 4) (by have := hL.below; omega)]
    have := hL.top; omega

theorem mul_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g m₀ t ∧
      Frame (mulWr L ++ [below L.E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((L.out + 32).setWidth 64) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 128).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 32).setWidth 64) 32) := by
  have cov := hash_covers (L := L) (rs := mulRd L ++ mulWr L) (by
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc hL.below scalarMulAdd_ok mul_nosp (by rw [mul_stack]; decide)
      (mul_pre hc hL ha) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨s₂, hm, _, hp⟩ := post
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt s₂.mem ((arg s.callEntry 0).setWidth 64) 32 = Spec.Ed25519.scalarMulAdd
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 2).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 3).setWidth 64) 32) at hp
  rw [hm, (ca (by decide)).trans ha.1, (ca (by decide)).trans ha.2.1,
    (ca (by decide)).trans ha.2.2.1, (ca (by decide)).trans ha.2.2.2.1] at hp
  rw [field_ce hc hL (d := 96) (by decide), field_ce hc hL (d := 128) (by decide),
    field_ce hc hL (d := 32) (by decide)] at hp
  exact hp

theorem mul_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (half L)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 128).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 32).setWidth 64) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  have a3 := hs.slot hL (j := 3) (by decide) (by decide)
  have a4 := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 4 = L.scr + 0#32 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hft, hp⟩ =>
    ⟨ht, primitive_frame hf hft, ?_⟩
  rw [half_addr hL, field_setup hL hf (d := 96) (by decide) (by decide),
    field_setup hL hf (d := 128) (by decide) (by decide),
    field_setup hL hf (d := 32) (by decide) (by decide)] at hp
  exact hp

end VG.Proof.Ed25519.X86.SignCached
