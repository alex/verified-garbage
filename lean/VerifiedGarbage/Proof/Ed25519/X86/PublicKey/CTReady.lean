import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash
import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Proof.Ed25519.X86.Whole.CallCT

/-! Merged from `Proof.Ed25519.X86.PublicKey.Setup`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup)

def argValue (s : State) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => esp s + BitVec.ofNat 32 d
  | .caller i d => arg s i + BitVec.ofNat 32 d

theorem setup_ok {s t : State} (h : Facts s) (hc : Ctx s t) {vs : List Value}
    (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v) :
    WP isa (.block (setup 0 vs)) t fun u => Ctx s u ∧
      Frame [⟨(esp s).setWidth 64, 24⟩] t.mem u.mem ∧
      ∀ j (hj : j < vs.length), Whole.slots (esp s) u j = argValue s (vs[j]'hj) := by
  refine WP.mono (Whole.Ctx.setup hc (n := 3) (by have := h.toBounds.frame; omega)
    (fun j hj => original_arg_readable h hc hj) (by omega) hv) fun u ⟨hu, hf, hs⟩ => ⟨hu, hf, ?_⟩
  intro j hj
  have e := hs j hj
  simp only [Nat.zero_add] at e
  rw [addr_eq (by have := h.toBounds.frame; omega)] at e
  rw [Whole.slots, e]
  generalize he : vs[j]'hj = v
  have vv := hv (vs[j]'hj) (List.getElem_mem hj)
  rw [he] at vv
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller i d =>
    exact congrArg (· + BitVec.ofNat 32 d) (original_arg h hc vv)

/-- Setup only writes the outgoing argument area, so unrelated buffers survive. -/
theorem setup_disjoint {s : State} (h : Facts s) :
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (SCR s) ∧
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (SEED s) ∧
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (OUT s) := by
  have sub : Region.Sub ⟨(esp s).setWidth 64, 24⟩ (Whole.STK (esp s)) :=
    fun p hp => Whole.frame_sub (esp s) p (Region.sub_prefix (by decide) p hp)
  exact ⟨h.kc.sub_left sub, h.ks.sub_left sub, h.ko.sub_left sub⟩

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Base`. -/
section
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
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Hash`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem hashSpace {s : State} (h : Facts s) : Whole.HashSpace (esp s) (arg s 2) :=
  ⟨h.toBounds.call, by have := h.toBounds.frame; omega, h.scratch, h.kc⟩

theorem shaWithin (s : State) : Whole.Within (Whole.SHA (arg s 2)) (SCR s) :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin {s : State} (h : Facts s) : Whole.Within (Whole.WORK (arg s 2)) (SCR s) :=
  ⟨192, (hashSpace h).work_addr, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (s : State) {n : Nat} (hn : n ≤ 256) :
    Whole.Within (Whole.ARGS (esp s) n) (Whole.FR (esp s)) := ⟨0, by simp, by change 0 + n ≤ 256; omega⟩

theorem hash_covers {s : State} {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR (esp s)) ∨ Whole.Within r (SCR s) ∨ Whole.Within r (SEED s)) :
    Covers rs (pkRd s ++ Whole.FR (esp s) :: pkWr s) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with h | h | h
  · exact ⟨_, by simp [pkRd, pkWr], h⟩
  · exact ⟨_, by simp [pkRd, pkWr], h⟩
  · exact ⟨_, by simp [pkRd, pkWr], h⟩

theorem hash_writes {s : State} {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR (esp s)) ∨ Whole.Within r (SCR s)) :
    ∀ r ∈ rs, Whole.Within r (Whole.FR (esp s)) ∨ ∃ R ∈ pkWr s, Whole.Within r R := by
  intro r hr
  rcases h r hr with h | h
  · exact .inl h
  · exact .inr ⟨_, by simp [pkWr], h⟩

theorem seed_same {s t : State} (h : Facts s) (hc : Ctx s t) :
    Spec.Ed25519.bytesAt t.mem ((arg s 1).setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32 := by
  apply List.map_congr_left
  intro i hi
  exact hc.frame.bytes (R := SEED s) (by
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.os.symm
    · exact h.sc
    · exact h.ks.symm) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem setup_repr {s t u : State} (h : Facts s)
    (hf : Frame [⟨(esp s).setWidth 64, 24⟩] t.mem u.mem) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem ((arg s 2).setWidth 64) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem ((arg s 2).setWidth 64) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := t.mem) ?_ hr
  intro i hi
  exact hf.bytes (R := Whole.SHA (arg s 2)) (by
    rintro r hr; rw [List.mem_singleton.mp hr]
    exact ((setup_disjoint h).1.sub_right Whole.HashSpace.sha_sub).symm) (by change 192 ≤ 2 ^ 64; decide) hi

theorem init_step {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512)) t
      fun u => Ctx s u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem ((arg s 2).setWidth 64) [] := by
  refine WP.seq (WP.mono (setup_ok h hc (vs := [.caller 2 0]) (by decide) (by simp [Whole.valid]))
    fun u ⟨hu, _, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  change Whole.slots (esp s) u 0 = arg s 2 + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have H := hashSpace h
  have hp := Whole.init_pre hu.esp H a0
  have cov : Covers (Whole.initRd (esp s) ++ Whole.initWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s)))
  have ws := hash_writes (s := s) (rs := Whole.initWr (arg s 2)) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin s))
  refine WP.mono (Whole.init_call hu H.below hp cov ws
    ((Whole.call_arg hu.esp H.below H.frameFit (by decide)).trans a0)) fun u ⟨hu, _, hr⟩ => ⟨hu, hr⟩

theorem update_step {s t : State} (h : Facts s) (hc : Ctx s t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem ((arg s 2).setWidth 64) []) :
    WP isa (callWith updateArgs Spec.Sha512.updateApi.name Impl.Sha512.X86.Stream.update) t
      fun u => Ctx s u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem ((arg s 2).setWidth 64)
        (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (setup_ok h hc
    (vs := [.caller 2 0, .const 0, .const 0, .caller 1 0, .const 32, .caller 2 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  have a5 := hs 5 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  have H := hashSpace h
  have hp := Whole.update_pre hu.esp H a0 a3 a4 a5 h.sc
    (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))) h.seed
  have cov : Covers (Whole.updateRd (esp s) (arg s 1) 32 ++ Whole.hashWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inr (.inr ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.hashWr (arg s 2)) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inr (workWithin h))
  have ce : ∀ j < 64, arg u.callEntry j = Whole.slots (esp s) u j :=
    fun j hj => Whole.call_arg hu.esp H.below H.frameFit hj
  have count : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 ([] : List Byte).length := by
    rw [Proof.Sha512.countX86, ce 1 (by decide), ce 2 (by decide), a1, a2]
    rfl
  refine WP.mono (Whole.update_call hu H.below hp cov ws
    ((ce 0 (by decide)).trans a0) ((ce 3 (by decide)).trans a3) ((ce 4 (by decide)).trans a4) count
    (by rw [hu.esp]; exact (H.below_sha (by decide)).symm)
    (by rw [hu.esp]; exact (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))).symm)
    (setup_repr h hf hr)) fun v ⟨hv, _, hr⟩ => ⟨hv, ?_⟩
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem ((arg s 1).setWidth 64) 32) at hr
  rw [List.nil_append, seed_same h hu] at hr
  exact hr

/-- The frame's digest pointer. -/
def digestPtr (s : State) : BitVec 32 := esp s + BitVec.ofNat 32 192

theorem digest_addr {s : State} (h : Facts s) :
    (digestPtr s).setWidth 64 = (esp s).setWidth 64 + BitVec.ofNat 64 192 :=
  addr_eq (by have := h.toBounds.frame; omega)

theorem finalize_step {s t : State} (h : Facts s) (hc : Ctx s t)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem ((arg s 2).setWidth 64)
      (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)) :
    WP isa (callWith finalizeArgs Spec.Sha512.finalizeApi.name Impl.Sha512.X86.Stream.finalize) t
      fun u => Ctx s u ∧ Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (setup_ok h hc
    (vs := [.caller 2 0, .const 32, .const 0, .frame 192, .caller 2 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4
  have H := hashSpace h
  have ds : Whole.Within ⟨(digestPtr s).setWidth 64, 64⟩ (Whole.FR (esp s)) :=
    ⟨192, digest_addr h, by change 192 + 64 ≤ 256; decide⟩
  have dd : Region.Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ (SCR s) :=
    h.kc.sub_left (fun p hp => Whole.frame_sub (esp s) p (ds.sub p hp))
  have db : (below (esp s) 24).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    change Region.Disjoint ⟨(esp s - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth H.below]
    exact Offset.disjoint_below_above _ (by decide)
  have da : (Whole.ARGS (esp s) 20).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have df : (digestPtr s).toNat + 64 ≤ 2 ^ 32 := by
    change (esp s + BitVec.ofNat 32 192).toNat + 64 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 192).toNat = 192 from rfl]
    have fe := H.frameFit
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 dd db da df
  have cov : Covers (Whole.finalizeRd (esp s) ++ Whole.finalizeWr (arg s 2) (digestPtr s))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inl ds
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.finalizeWr (arg s 2) (digestPtr s)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inl ds
    · exact .inr (workWithin h))
  have ce : ∀ j < 64, arg u.callEntry j = Whole.slots (esp s) u j :=
    fun j hj => Whole.call_arg hu.esp H.below H.frameFit hj
  have len : (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length = 32 := by
    simp [Spec.Ed25519.bytesAt]
  have count : Proof.Sha512.countX86 u.callEntry =
      BitVec.ofNat 64 (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32).length := by
    rw [Proof.Sha512.countX86, ce 1 (by decide), ce 2 (by decide), a1, a2, len]
    rfl
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws
    ((ce 0 (by decide)).trans a0) ((ce 3 (by decide)).trans a3) count
    (by rw [hu.esp]; exact (H.below_sha (by decide)).symm)
    (setup_repr h hf hr) (by rw [len]; decide)) fun v ⟨hv, _, hd⟩ => ⟨hv, ?_⟩
  change Spec.Ed25519.bytesAt v.mem ((digestPtr s).setWidth 64) 64 = _ at hd
  rw [digest_addr h] at hd
  exact hd

theorem hash_ok {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa hash t fun u => Ctx s u ∧ Spec.Sha512.bytesAt u.mem ((esp s).setWidth 64 + 192) 64 =
      Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) :=
  WP.seq (WP.mono (init_step h hc) fun _ ⟨hc, hr⟩ =>
    WP.seq (WP.mono (update_step h hc hr) fun _ ⟨hc, hr⟩ => finalize_step h hc hr))

end VG.Proof.Ed25519.X86.PublicKey
end

/-! Merged from `Proof.Ed25519.X86.PublicKey.Correct`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem prune_step {s t : State} (h : Facts s) (hc : Ctx s t) {digest : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx s u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prune_ok hc.esp (by have := h.toBounds.frame; omega)
    (by rw [hc.wr]; exact List.mem_cons_self) hh) fun u ⟨ku, hf, hs⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame ku.rd ku.wr ku.esp ?_ hf ?_
    · intro r hr _
      apply ku.regs
      rintro rfl
      simp [calleeSaved] at hr
    · rintro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by decide))
  · rw [scalarPtr_addr h.toBounds]
    exact hs

theorem base_step {s t : State} (h : Facts s) (hc : Ctx s t) {n : Nat}
    (hn : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) t
      fun u => Ctx s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (setup_ok h hc (vs := [.caller 0 0, .frame 32, .caller 2 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have he : Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := ⟨(scalarPtr s).setWidth 64, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr, scalarPtr_addr h.toBounds]
      exact Offset.disjoint_base _ (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  refine WP.mono (base_call h hu ⟨a0, a1, a2⟩) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  rw [ho, he, Spec.Ed25519.scalarBase, hn]

theorem body_ok {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa body t fun u => Ctx s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (hash_ok h hc) fun t₁ ⟨hc₁, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step h hc₁ hh) fun t₂ ⟨hc₂, hn⟩ => ?_)
  refine WP.seq (WP.mono (base_step h hc₂ hn) fun t₃ ⟨hc₃, ho⟩ => ?_)
  refine WP.mono (Whole.Ctx.zeroWords hc₃ (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  have he : Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₃.mem ((arg s 0).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := OUT s) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact (h.ko.sub_left (fun p hp => Whole.frame_sub (esp s) p
        (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm)
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [he, ho]
  rfl

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem body_nosp : NoSp body := by
  have ni : NoSp (.block initArgs) := NoSp.of_all (by decide +kernel)
  have nu : NoSp (.block updateArgs) := NoSp.of_all (by decide +kernel)
  have nf : NoSp (.block finalizeArgs) := NoSp.of_all (by decide +kernel)
  have nb : NoSp (.block baseArgs) := NoSp.of_all (by decide +kernel)
  have np : NoSp (.block prune) := NoSp.of_all (by decide +kernel)
  have nw : NoSp (.block wipe) := NoSp.of_all (by decide +kernel)
  exact noSp_seq
    (noSp_seq (noSp_seq ni Whole.init_nosp)
      (noSp_seq (noSp_seq nu Whole.update_nosp) (noSp_seq nf Whole.finalize_nosp)))
    (noSp_seq np (noSp_seq (noSp_seq nb base_nosp) nw))

theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa publicKey s fun t => abiPreserved s t ∧ pkLocal.post s t := by
  have hf := facts h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := hf.below; omega) body_nosp
    (WP.mono (body_ok hf (push_ctx h)) fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := RET s) (Region.contains_self _ _) ?_ (by decide)
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hf.ro
    · exact hf.rc
    · rw [stack_eq hf.toBounds]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 280).setWidth 64, 280⟩
      rw [Taint.sub_setWidth hf.below]
      exact (Offset.below_disjoint _ (by decide)).symm
  · change Spec.Ed25519.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem
      ((arg s 0).setWidth 64) 32 = _
    rw [popped_mem]
    exact ho

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value)

def Slots (vs : List Value) (s t : State) : Prop :=
  ∀ j (hj : j < vs.length), Whole.slots (esp s) t j = argValue s (vs[j]'hj)

def initValues : List Value := [.caller 2 0]
def updateValues : List Value := [.caller 2 0, .const 0, .const 0, .caller 1 0, .const 32, .caller 2 192]
def finalizeValues : List Value := [.caller 2 0, .const 32, .const 0, .frame 192, .caller 2 192]
def baseValues : List Value := [.caller 0 0, .frame 32, .caller 2 0]

def init_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots initValues s t) :
    Whole.CallReady (Proof.Sha512.initX86 Spec.Sha512.H0_512) (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < initValues.length), Whole.slots (esp s) t j = argValue s (initValues[j]'hj) at hs
  unfold initValues at hs
  have a0 := hs 0 (by decide)
  change Whole.slots (esp s) t 0 = arg s 2 + 0#32 at a0
  rw [BitVec.add_zero] at a0
  have H := hashSpace h
  have hp := Whole.init_pre hc.esp H a0
  have cov : Covers (Whole.initRd (esp s) ++ Whole.initWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.initRd, Whole.initWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s)))
  have ws := hash_writes (s := s) (rs := Whole.initWr (arg s 2)) (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact .inr (shaWithin s))
  exact ⟨Whole.initRd (esp s), Whole.initWr (arg s 2), hp, cov, ws⟩

def update_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots updateValues s t) :
    Whole.CallReady Proof.Sha512.updateX86 (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < updateValues.length), Whole.slots (esp s) t j = argValue s (updateValues[j]'hj) at hs
  unfold updateValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  have a5 := hs 5 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  have H := hashSpace h
  have hp := Whole.update_pre hc.esp H a0 a3 a4 a5 h.sc
    (h.ks.sub_left (Whole.below_sub_stack H.below (by decide))) h.seed
  have cov : Covers (Whole.updateRd (esp s) (arg s 1) 32 ++ Whole.hashWr (arg s 2))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inr (.inr ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.hashWr (arg s 2)) (by
    simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inr (workWithin h))
  exact ⟨Whole.updateRd (esp s) (arg s 1) 32, Whole.hashWr (arg s 2), hp, cov, ws⟩

def finalize_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots finalizeValues s t) :
    Whole.CallReady Proof.Sha512.finalizeX86 (esp s) (pkRd s) (pkWr s) t := by
  change ∀ j (hj : j < finalizeValues.length), Whole.slots (esp s) t j = argValue s (finalizeValues[j]'hj) at hs
  unfold finalizeValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  have a3 := hs 3 (by decide)
  have a4 := hs 4 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4
  have H := hashSpace h
  have ds : Whole.Within ⟨(digestPtr s).setWidth 64, 64⟩ (Whole.FR (esp s)) :=
    ⟨192, digest_addr h, by change 192 + 64 ≤ 256; decide⟩
  have dd : Region.Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ (SCR s) :=
    h.kc.sub_left (fun p hp => Whole.frame_sub (esp s) p (ds.sub p hp))
  have db : (below (esp s) 24).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    change Region.Disjoint ⟨(esp s - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth H.below]
    exact Offset.disjoint_below_above _ (by decide)
  have da : (Whole.ARGS (esp s) 20).Disjoint ⟨(digestPtr s).setWidth 64, 64⟩ := by
    rw [digest_addr h]
    exact Offset.base_disjoint _ (by decide) (by decide)
  have df : (digestPtr s).toNat + 64 ≤ 2 ^ 32 := by
    change (esp s + BitVec.ofNat 32 192).toNat + 64 ≤ 2 ^ 32
    rw [BitVec.toNat_add, show (BitVec.ofNat 32 192).toNat = 192 from rfl]
    have fe := H.frameFit
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp := Whole.finalize_pre hc.esp H a0 a3 a4 dd db da df
  have cov : Covers (Whole.finalizeRd (esp s) ++ Whole.finalizeWr (arg s 2) (digestPtr s))
      (pkRd s ++ Whole.FR (esp s) :: pkWr s) := hash_covers (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin s (by decide))
    · exact .inr (.inl (shaWithin s))
    · exact .inl ds
    · exact .inr (.inl (workWithin h)))
  have ws := hash_writes (s := s) (rs := Whole.finalizeWr (arg s 2) (digestPtr s)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin s)
    · exact .inl ds
    · exact .inr (workWithin h))
  exact ⟨Whole.finalizeRd (esp s), Whole.finalizeWr (arg s 2) (digestPtr s), hp, cov, ws⟩

def base_ready {s t : State} (h : Facts s) (hc : Ctx s t) (hs : Slots baseValues s t) :
    Whole.CallReady scalarBaseLocal (esp s) (pkRd s) (pkWr s) t := by
  unfold Slots baseValues at hs
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have ha : BaseArgs s t := ⟨a0, a1, a2⟩
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
  exact ⟨baseRd s, pkWr s, base_pre h hc ha, cov, ws⟩

end VG.Proof.Ed25519.X86.PublicKey
