import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Count
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Hash`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.PublicKey (callWith)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSpace (h : L.Ok) : Whole.HashSpace L.E L.scr :=
  ⟨h.below, by have := h.top; omega, h.nc, h.kc⟩

theorem shaWithin (L : Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩

theorem workWithin (h : L.Ok) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, (hashSpace h).work_addr, by change 192 + 272 ≤ 8192; decide⟩

theorem argsWithin (L : Lay) {n : Nat} (hn : n ≤ 256) :
    Whole.Within (Whole.ARGS L.E n) L.FR := ⟨0, by simp, by simpa using hn⟩

theorem hash_covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with h | ⟨R, hR, h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨R, by simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using Or.inr hR, h⟩

theorem hash_writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with h | h
  · exact .inl h
  · exact .inr ⟨_, by simp [Lay.outputs], h⟩

theorem scratch_covered {r : Region} (h : Whole.Within r L.SCR) :
    Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  .inr ⟨_, by simp [Lay.outputs], h⟩

def hashWrites (L : Lay) : List Region :=
  [L.SCR, ⟨L.E.setWidth 64, 24⟩, below L.E 24, ⟨L.E.setWidth 64 + 192, 64⟩]

theorem setup_frame {m m' : Mem} (h : Frame [⟨L.E.setWidth 64, 24⟩] m m') : Frame (hashWrites L) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [hashWrites], fun _ h => h⟩

theorem hash_frame {m m' : Mem} {wr : List Region}
    (h : Frame (wr ++ [below L.E 24]) m m')
    (hw : ∀ r ∈ wr, Whole.Within r L.SCR ∨ Whole.Within r ⟨L.E.setWidth 64 + 192, 64⟩) :
    Frame (hashWrites L) m m' := by
  refine h.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with h | h
    · exact ⟨_, by simp [hashWrites], h.sub⟩
    · exact ⟨_, by simp [hashWrites], h.sub⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp [hashWrites], fun _ h => h⟩

theorem setup_repr (hL : L.Ok) {u : State}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem (L.scr.setWidth 64) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := s.mem) ?_ hr
  intro i hi
  exact hf.bytes (R := Whole.SHA L.scr) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact ((hashSpace hL).args_sha (n := 24) (by decide)).symm) (by change 192 ≤ 2 ^ 64; decide) hi

theorem OutArgs.slot {vs : List Value} {t : State} (h : OutArgs L vs t) (hL : L.Ok)
    {j : Nat} (hj : j < vs.length) (hlen : vs.length ≤ 6) :
    Whole.slots L.E t j = value L (vs[j]'hj) := by
  have e := h j hj
  rw [addr_eq (by have := hL.top; omega)] at e
  exact e

theorem init_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa Impl.Ed25519.X86.VerifyMessage.init s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64) [] := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.caller 4 0]) (by decide) (by simp [Whole.valid]))
    fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 : Whole.slots L.E u 0 = L.scr := by
    have hh := hs.slot hL (j := 0) (by decide) (by decide)
    change Whole.slots L.E u 0 = L.scr + BitVec.ofNat 32 0 at hh
    simpa only [BitVec.add_zero] using hh
  have H := hashSpace hL
  have cov := hash_covers (L := L) (rs := Whole.initRd L.E ++ Whole.initWr L.scr) (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L))
  have ws := hash_writes (L := L) (rs := Whole.initWr L.scr) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin L))
  refine WP.mono (Whole.init_call hu H.below (Whole.init_pre hu.esp H a0) cov ws
    ((Whole.call_arg hu.esp H.below H.frameFit (by decide)).trans a0)) fun t ⟨ht, hft, hr⟩ =>
    ⟨ht, (setup_frame hf).trans (hash_frame hft ?_), hr⟩
  intro r hr; rw [List.mem_singleton.mp hr]; exact .inl (shaWithin L)

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Equation`. -/
section
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
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashFinalize`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.FinalizeArgs`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole VG.Impl.Ed25519.X86.VerifyMessage

def FinArgs (L : Lay) (count : BitVec 64) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 3 = L.E + 192 ∧
    Whole.slots L.E t 4 = L.scr + 192 ∧
    Whole.slots L.E t 2 ++ Whole.slots L.E t 1 = count

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_keep {t u : State} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] t.mem u.mem)
    {j : Nat} (hj : j = 0 ∨ j = 3 ∨ j = 4) : Whole.slots L.E u j = Whole.slots L.E t j := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  apply Offset.disjoint (e := 4) (k := 8)
  · rcases hj with rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl <;> decide
  · decide

theorem count_frame {m m' : Mem} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] m m') :
    Frame [⟨L.E.setWidth 64, 24⟩] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (d := 4) (by decide)⟩

theorem finalizeArgs_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    :
    WP isa (.block finalizeArgs) s fun t => Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧
      FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)) t := by
  rw [finalizeArgs, WP.block_append_iff]
  refine WP.mono (args_ok hc hL ha (vs := [.caller 4 0, .const 0, .const 0, .frame 192, .caller 4 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_
  have aa := hs.slot hL (j := 0) (by decide) (by decide)
  have ab := hs.slot hL (j := 1) (by decide) (by decide)
  have ac := hs.slot hL (j := 2) (by decide) (by decide)
  have ad := hs.slot hL (j := 3) (by decide) (by decide)
  have ae := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.scr + 0#32 at aa
  rw [BitVec.add_zero] at aa
  change Whole.slots L.E u 1 = 0#32 at ab
  change Whole.slots L.E u 2 = 0#32 at ac
  change Whole.slots L.E u 3 = L.E + 192 at ad
  change Whole.slots L.E u 4 = L.scr + 192 at ae
  have hr : InRegions (u.rd ++ u.wr) (addr L.E 268) 4 := by
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hu.rd]; simp [Lay.inputs]
    · rw [addr_eq (by have := hL.top; omega)]
      exact Offset.contains _ (e := 260) (k := 20) (d := 268) (n := 4) (by decide) (by decide) (by decide)
  have hx : u.mem.readW (addr L.E 268) 32 = L.len := by
    rw [addr_eq (by have := hL.top; omega)]
    exact (hu.arg_word hL (j := 2) (by decide)).trans (ha 2 (by decide))
  refine WP.mono (Whole.Ctx.count hu (index := 2) (n := 64) (by have := hL.top; omega) hr hx)
    fun t ⟨ht, hft, hlo, hhi⟩ => ⟨ht, hf.trans (count_frame hft),
      (count_keep hft (.inl rfl)).trans aa,
      (count_keep hft (.inr (.inl rfl))).trans ad,
      (count_keep hft (.inr (.inr rfl))).trans ae, ?_⟩
  show (t.mem.readW (L.E.setWidth 64 + 8#64) 32 ++ t.mem.readW (L.E.setWidth 64 + 4#64) 32) = BitVec.ofNat 64 (L.len.toNat + 64)
  change t.mem.readW (L.E.setWidth 64 + 8#64) 32 = _ at hhi
  change t.mem.readW (L.E.setWidth 64 + 4#64) 32 = _ at hlo
  rw [hhi, hlo]
  exact Whole.count_pair L.len 64 (by decide)

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem digest_addr (hL : L.Ok) : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
  addr_eq (x := L.E) (k := 192) (by have := hL.top; omega)

theorem digestWithin (hL : L.Ok) : Whole.Within ⟨(L.E + 192).setWidth 64, 64⟩ L.FR :=
  ⟨192, digest_addr hL, by change 192 + 64 ≤ 256; decide⟩

theorem digest_below (hL : L.Ok) : (below L.E 24).Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ := by
  change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
  rw [Taint.sub_setWidth hL.below, digest_addr hL]
  exact Offset.disjoint_below_above _ (m := 24) (a := 192) (l := 64) (by decide)

theorem finalize_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : L.len.toNat + 64 = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith finalizeArgs Spec.Sha512.finalizeApi.name Impl.Sha512.X86.Stream.finalize) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 msg := by
  refine WP.seq (WP.mono (finalizeArgs_ok hc hL ha) fun u ⟨hu, hf, a0, a3, a4, ac⟩ => ?_)
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), ac, hcount]
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) cnt hbsha (setup_repr hL hf hr) hlen)
    fun t ⟨ht, hft, hdigest⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inr ⟨0, by rw [digest_addr hL]; simp, by change 0 + 64 ≤ 64; decide⟩
    · exact .inl (workWithin hL)
  · rw [digest_addr hL] at hdigest
    exact hdigest

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashInputs`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashUpdate`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

structure Input (L : Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨p.setWidth 64, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R
  scratch : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR
  below : (below L.E 24).Disjoint ⟨p.setWidth 64, n.toNat⟩
  args : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ ⟨L.E.setWidth 64, 24⟩
  fit : p.toNat + n.toNat ≤ 2 ^ 32

def UpdateArgs (L : Lay) (c p n : BitVec 32) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 1 = c ∧ Whole.slots L.E t 2 = 0 ∧
    Whole.slots L.E t 3 = p ∧ Whole.slots L.E t 4 = n ∧ Whole.slots L.E t 5 = L.scr + 192

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

theorem update_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v)
    {c p n : BitVec 32} (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t)
    (hi : Input L p n) {prev : List Byte} (hcount : c.toNat = prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (setup 0 vs)) s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat) := by
  refine WP.seq (WP.mono (args_ok hc hL ha hlen hv) fun u ⟨hu, hf, hs⟩ => ?_)
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hargs u hs
  have H := hashSpace hL
  have hp := Whole.update_pre hu.esp H a0 a3 a4 a5 hi.scratch hi.below hi.fit
  have cov := hash_covers (L := L) (rs := Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hi.cover
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.hashWr L.scr) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 prev.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), a1, a2]
    exact (count_zero_high c).trans (congrArg (BitVec.ofNat 64) hcount)
  have hb : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ (below (u.gpr .esp) 4) := by
    rw [hu.esp]
    exact (hi.below.sub_left (below_sub (by decide) H.below)).symm
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.update_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) (ca (by decide) |>.trans a4) cnt hbsha hb
    (setup_repr hL hf hr)) fun t ⟨ht, hft, hrepr⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inl (workWithin hL)
  · have same : Spec.Ed25519.bytesAt u.mem (p.setWidth 64) n.toNat =
        Spec.Ed25519.bytesAt s.mem (p.setWidth 64) n.toNat := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi' => ?_
      exact hf.bytes (R := ⟨p.setWidth 64, n.toNat⟩)
        (by rintro r hr; rw [List.mem_singleton.mp hr]; exact hi.args)
        (by have := n.isLt; change n.toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi')
    rw [same] at hrepr
    exact hrepr

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem input_geometry (hL : L.Ok) {p n : BitVec 32} {R : Region}
    (hr : R ∈ L.inputs) (hw : Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hf : p.toNat + n.toNat ≤ 2 ^ 32) : Input L p n := by
  refine ⟨.inr ⟨R, List.mem_append_left _ hr, hw⟩, (hL.sc _ hr).sub_left hw.sub,
    ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by simp))).sub_right hw.sub, ?_, hf⟩
  exact ((hL.ks _ hr).sub_left (fun p hp => Whole.frame_sub L.E p
    ((argsWithin L (n := 24) (by simp)).sub p hp))).symm.sub_left hw.sub

theorem input_pk (hL : L.Ok) : Input L L.pk 32 :=
  input_geometry hL (R := L.PK) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩ hL.np

theorem input_sig (hL : L.Ok) : Input L L.sig 32 :=
  input_geometry hL (R := L.SIG) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (by change L.sig.toNat + 32 ≤ 2 ^ 32; have := hL.ns; omega)

theorem input_msg (hL : L.Ok) : Input L L.msg L.len :=
  input_geometry hL (R := L.MSG) (by simp [Lay.inputs]) ⟨0, by simp, by simp⟩ hL.nm

theorem prefix_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {source count : Nat} (hs : source < 5) {prev : List Byte}
    (hlen : prev.length = count) (hcount : count < 2 ^ 32)
    (hi : Input L (L.value source) 32)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (Impl.Ed25519.X86.VerifyMessage.prefixArgs source count)) s
      fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  apply update_step hc hL ha (vs := [.caller 4 0, .const count, .const 0,
    .caller source 0, .const 32, .caller 4 192]) (by simp)
    (by simp [Whole.valid, hs]) (c := BitVec.ofNat 32 count) (p := L.value source) (n := 32)
    ?_ hi (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount] using hlen.symm) hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 4) (by simp) (by simp)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

theorem message_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {prev : List Byte} (hlen : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update Impl.Ed25519.X86.VerifyMessage.messageArgs) s
      fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.msg.setWidth 64) L.len.toNat) := by
  apply update_step hc hL ha (vs := [.caller 4 0, .const 64, .const 0,
    .caller 1 0, .caller 2 0, .caller 4 192]) (by simp)
    (by simp [Whole.valid]) (c := 64) (p := L.msg) (n := L.len)
    ?_ (input_msg hL) hlen.symm hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact (ht.slot hL (j := 4) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

end VG.Proof.Ed25519.X86.VerifyMessage
end

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.X86.VerifyMessage.HashPipeline`. -/
section
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem hash_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hash s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun t ⟨ht, _, hinit⟩ => ?_)
  refine WP.seq (WP.mono (prefix_step ht hL ha (source := 3) (count := 0)
    (by decide) rfl (by decide) (input_sig hL) hinit) fun u ⟨hu, _, hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (L.sig.setWidth 64) 32) at hsig
  rw [List.nil_append, sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (prefix_step hu hL ha (source := 0) (count := 32)
    (by decide) (bytes_length _ _ _) (by decide) (input_pk hL) hsig) fun v ⟨hv, _, hpk⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (L.pk.setWidth 64) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32).length = 64 := by
    rw [List.length_append, bytes_length, bytes_length]
  refine WP.seq (WP.mono (message_step hv hL ha hpkl hpk) fun w ⟨hw, _, hmsg⟩ => ?_)
  rw [hv.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega)] at hmsg
  have hlen : (hashInput L m₀).length = L.len.toNat + 64 := by
    simp only [hashInput, List.length_append, bytes_length]
    omega
  refine WP.mono (finalize_step hw hL ha (msg := hashInput L m₀)
    (by rw [hlen]; have := L.len.isLt; omega) hlen.symm hmsg) fun t ⟨ht, _, hd⟩ => ⟨ht, hd⟩

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.X86.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem setup_bytes {u : State} {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] s.mem u.mem) (hd : 24 ≤ d) (hn : d + n ≤ 256) :
    Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact (Offset.base_disjoint _ hd (by omega)).symm) (by change n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce) s
      fun t => Ctx L g m₀ t ∧ Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.frame 128, .frame 192, .caller 4 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := (hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _)
  have H := hashSpace hL
  refine WP.mono (Whole.reduce_call hu H (by simp [Lay.outputs]) (d := 128)
    (by decide) (by decide) a0 a1 a2) fun t ⟨ht, _, hd⟩ => ⟨ht, ?_⟩
  have e128 : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 := Whole.frame_addr H.frameFit (by decide : 128 < 256)
  have e192 : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 := Whole.frame_addr H.frameFit (by decide : 192 < 256)
  change Spec.Ed25519.bytesAt t.mem ((L.E + 128).setWidth 64) 32 = _ at hd
  have same : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 192) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 :=
    setup_bytes hf (by decide : 24 ≤ 192) (by decide : 192 + 64 ≤ 256)
  rw [e128, e192, same] at hd
  exact hd

theorem extend_step (hc : Ctx L g m₀ s) (hL : L.Ok) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 40) (count := 8)
    (hashSpace hL).frameFit (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E.setWidth 64 + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.X86.encodeLE_eq]
    apply Proof.X25519.bytesAt_leBytes_words32
    intro j hj
    have z := hz j hj
    rw [addr_eq (by have := hL.top; omega)] at z
    have e : L.E.setWidth 64 + BitVec.ofNat 64 (4 * (40 + j)) =
        L.E.setWidth 64 + 160 + BitVec.ofNat 64 (4 * j) := by
      rw [show 4 * (40 + j) = 160 + 4 * j by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [e] at z
    rw [z]
    simp
  change Spec.X25519.bytesAt t.mem (L.E.setWidth 64 + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128 + 32) 32 = _
  rw [show L.E.setWidth 64 + 128 + 32 = L.E.setWidth 64 + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 ++
      Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 64).take 32 =
      Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem equation_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {challenge : List Byte}
    (hh : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = challenge) :
    WP isa (VG.Impl.Ed25519.X86.PublicKey.callWith equationArgs "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation) s
      fun t => Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64) challenge) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (vs := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  have a1 := (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  have a3 := (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)
  have he : Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + 128) 64 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 :=
    setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)
  refine WP.mono (equation_call hu hL ⟨a0, a1, a2, a3⟩) fun t ⟨ht, eq⟩ => ⟨ht, ?_⟩
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide),
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide), he, hh] at eq
  exact eq

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa body s fun t => Ctx L g m₀ t ∧ t.gpr .eax = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32)
      (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat)
      (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 64)) := by
  refine WP.seq (WP.mono (hash_ok hc hL ha) fun t ⟨ht, hh⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step ht hL ha) fun u ⟨hu, hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (extend_step hu hL hr) fun v ⟨hv, he⟩ => ?_)
  rw [hashInput_eq] at he
  exact equation_step hv hL ha he

end VG.Proof.Ed25519.X86.VerifyMessage
