import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre

namespace VG.Proof.Ed25519.X86.SignCached
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
    WP isa Impl.Ed25519.X86.SignCached.init s fun t => Ctx L g m₀ t ∧
      Frame (hashWrites L) s.mem t.mem ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64) [] := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.caller 5 0]) (by decide) (by simp [Whole.valid]))
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

end VG.Proof.Ed25519.X86.SignCached
