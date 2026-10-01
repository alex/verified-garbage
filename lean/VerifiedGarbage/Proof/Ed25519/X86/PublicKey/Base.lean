import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Setup
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86 (scalarBase)

def scalarPtr (s : State) : BitVec 32 := esp s + BitVec.ofNat 32 32

theorem scalarPtr_addr {s : State} (h : Bounds s) :
    (scalarPtr s).setWidth 64 = (esp s).setWidth 64 + BitVec.ofNat 64 32 :=
  addr_eq (by have := h.frame; omega)

theorem base_nosp : NoSp scalarBase := NoSp.of_all (by lit_decide)
theorem base_stack : stackUse scalarBase = 0 := by lit_decide

def BaseArgs (s t : State) : Prop :=
  Whole.slots (esp s) t 0 = arg s 0 ∧ Whole.slots (esp s) t 1 = scalarPtr s ∧
    Whole.slots (esp s) t 2 = arg s 2

def baseRd (s : State) : List Region := [⟨(scalarPtr s).setWidth 64, 32⟩, ⟨(esp s).setWidth 64, 12⟩]

/-- The three cdecl argument slots of the base-point multiplication. -/
theorem base_args {s t : State} (h : Facts s) (hc : Ctx s t) (ha : BaseArgs s t) :
    arg t.callEntry 0 = arg s 0 ∧ arg t.callEntry 1 = scalarPtr s ∧ arg t.callEntry 2 = arg s 2 := by
  have e : ∀ j < 64, arg t.callEntry j = Whole.slots (esp s) t j :=
    fun j hj => Whole.call_arg hc.esp h.toBounds.call (by have := h.toBounds.frame; omega) hj
  exact ⟨(e 0 (by decide)).trans ha.1, (e 1 (by decide)).trans ha.2.1,
    (e 2 (by decide)).trans ha.2.2⟩

theorem base_pre {s t : State} (h : Facts s) (hc : Ctx s t) (ha : BaseArgs s t) :
    scalarBaseLocal.pre (t.callEntry.withRegions (baseRd s) (pkWr s)) := by
  obtain ⟨a0, a1, a2⟩ := base_args h hc ha
  have ae : argAddr t.callEntry 0 = (esp s).setWidth 64 := by
    rw [argAddr_callEntry, hc.esp]
    simp
  have fe := h.toBounds.frame
  have be := h.toBounds.call
  have ret : Region.Sub ⟨(esp s - 4).setWidth 64, 4⟩ (Whole.STK (esp s)) :=
    Whole.below_sub_stack be (by decide)
  have args : Region.Sub ⟨(esp s).setWidth 64, 12⟩ (Whole.STK (esp s)) :=
    fun p hp => Whole.frame_sub (esp s) p (Region.sub_prefix (by decide) p hp)
  have scalar : Region.Sub ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.STK (esp s)) := by
    rw [scalarPtr_addr h.toBounds]
    exact fun p hp => Whole.frame_sub (esp s) p (Offset.sub_base _ (by decide : 32 + 32 ≤ 256) p hp)
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    argAddr_withRegions, State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, ae]
  refine ⟨rfl, rfl, h.oc, h.kc.sub_left scalar, h.ko.sub_left args, h.kc.sub_left args,
    h.ko.sub_left ret, h.kc.sub_left ret, h.out, ?_, h.scratch, ?_⟩
  · change (esp s + BitVec.ofNat 32 32).toNat + 32 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  · change (esp s - BitVec.ofNat 32 4).toNat + 16 ≤ 2 ^ 32
    rw [sub_toNat (by omega : 4 ≤ (esp s).toNat)]
    omega

theorem base_call {s t : State} (h : Facts s) (hc : Ctx s t) (ha : BaseArgs s t) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) t fun u => Ctx s u ∧
      Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) := by
  have scalarWithin : Whole.Within ⟨(scalarPtr s).setWidth 64, 32⟩ (Whole.FR (esp s)) :=
    ⟨32, scalarPtr_addr h.toBounds, by change 32 + 32 ≤ 256; decide⟩
  have cov : Covers (baseRd s ++ pkWr s) (pkRd s ++ Whole.FR (esp s) :: pkWr s) := by
    refine Covers.of_sub ?_
    simp only [baseRd, pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨Whole.FR (esp s), by simp, scalarWithin⟩
    · exact ⟨Whole.FR (esp s), by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨OUT s, by simp, 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    · exact ⟨SCR s, by simp, 0, by simp, by change 0 + 8192 ≤ 8192; decide⟩
  have ws : ∀ r ∈ pkWr s, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R :=
    fun r hr => .inr ⟨r, hr, 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc h.toBounds.call scalarBase_ok base_nosp (by rw [base_stack]; decide)
      (base_pre h hc ha) cov ws fun u hu _ _ post => ⟨hu, ?_⟩
  obtain ⟨s₂, hm, hg, hp⟩ := post
  obtain ⟨a0, a1, _⟩ := base_args h hc ha
  change Spec.Ed25519.bytesAt s₂.mem ((arg t.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt t.callEntry.mem ((arg t.callEntry 1).setWidth 64) 32) at hp
  rw [hm, a0, a1] at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarBase ?_
  refine Whole.callEntry_bytes (r := ⟨(scalarPtr s).setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide)
  rw [hc.esp, scalarPtr_addr h.toBounds]
  change Region.Disjoint ⟨(esp s).setWidth 64 + BitVec.ofNat 64 32, 32⟩
    ⟨(esp s - BitVec.ofNat 32 4).setWidth 64, 4⟩
  have e : (esp s - BitVec.ofNat 32 4).setWidth 64 = (esp s).setWidth 64 - BitVec.ofNat 64 4 :=
    Taint.sub_setWidth (m := 4) (by have := h.toBounds.call; omega)
  rw [e]
  exact (Offset.disjoint_below_above _ (m := 4) (a := 32) (l := 32) (by decide)).symm

end VG.Proof.Ed25519.X86.PublicKey
