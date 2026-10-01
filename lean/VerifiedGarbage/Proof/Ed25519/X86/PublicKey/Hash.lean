import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Setup
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre

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
