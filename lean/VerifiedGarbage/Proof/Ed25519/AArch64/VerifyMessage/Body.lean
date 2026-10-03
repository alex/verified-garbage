import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Hash`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hash_writes : ∀ r ∈ Whole.hashWr L.scr,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  Whole.hash_writes (by simp [Lay.outputs])

theorem init_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g v m₀ t ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  unfold init VG.Impl.Ed25519.AArch64.Whole.callWith initArgs
  apply WP.seq
  refine WP.mono (args_ok hc hL ha (args := [(.x0,.caller 4 0)]) (by decide) (by simp [Whole.valid]) (by simp [known]) (by decide)) ?_
  intro t ⟨ht, _, hv⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hv (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have hw := Whole.init_writes (E := L.E) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call ht (Whole.init_pre a0)
    (Whole.covers_writes hw) hw a0) fun u ⟨hu, _, hr⟩ => ⟨hu, hr⟩

/-- Append a known input buffer without depending on its contents. -/
theorem update_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {args : List (Reg × Value)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hk : ∀ p ∈ args, known p.2) (hregs : ∀ p ∈ args, p.1 ∉ preserved)
    {p len : Addr} {prev : List Byte}
    (hargs : ∀ t, OutArgs L args t → t.gpr .x0 = L.scr ∧
      t.gpr .x1 = BitVec.ofNat 64 prev.length ∧ t.gpr .x2 = p ∧
      t.gpr .x3 = len ∧ t.gpr .x4 = L.scr + 192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (setup args)) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem p len.toNat) := by
  unfold update VG.Impl.Ed25519.AArch64.Whole.callWith
  apply WP.seq
  refine WP.mono (args_ok hc hL ha hn hv hk hregs) ?_
  intro t ⟨ht, hm, hav⟩
  obtain ⟨a0,a1,a2,a3,a4⟩ := hargs t hav
  have hcov : Covers (Whole.updateRd p len ++ Whole.hashWr L.scr)
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
    refine Covers.of_sub fun R hR => ?_
    rcases List.mem_append.mp hR with hR | hR
    · simp only [Whole.updateRd, List.mem_singleton] at hR
      subst R
      obtain ⟨R,hR,hs⟩ := hi
      exact ⟨R,List.mem_append_left _ hR,hs⟩
    · rcases hash_writes R hR with hf | ⟨S,hS,hs⟩
      · exact ⟨Whole.FR L.E,List.mem_append_right _ List.mem_cons_self,hf⟩
      · exact ⟨S,List.mem_append_right _ (List.mem_cons_of_mem _ hS),hs⟩
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev := hm ▸ hr
  refine WP.mono (Whole.update_call backend ht (Whole.update_pre a0 a2 a3 a4 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact hL.ck_within hi))
    hcov hash_writes a0 a2 a3 a1 hr') fun u ⟨hu,_,huv⟩ => ⟨hu,?_⟩
  rw [hm] at huv
  exact huv

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Calls`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay}

def field (L : Lay) (d : Nat) : Region := ⟨L.E + BitVec.ofNat 64 d, 32⟩
def digest (L : Lay) : Region := ⟨L.E + BitVec.ofNat 64 192, 64⟩

theorem fieldWithin (L : Lay) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (field L d) L.FR :=
  ⟨d, rfl, hd⟩
theorem digestWithin (L : Lay) : Whole.Within (digest L) L.FR := ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
theorem scratchWithin (L : Lay) : Whole.Within L.SCR L.SCR := ⟨0, by simp, by simp⟩

theorem covers {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R) :
    Covers rs (L.inputs ++ L.FR :: L.outputs) := by
  apply Covers.of_sub
  intro r hr
  rcases h r hr with hf | ⟨R, hR, hsub⟩
  · exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hsub⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem scratch_covered (L : Lay) : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within L.SCR R :=
  ⟨L.SCR, by simp [Lay.outputs], scratchWithin L⟩

theorem writes {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r L.FR ∨ Whole.Within r L.SCR) :
    ∀ r ∈ rs, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rcases h r hr with hf | hs
  · exact .inl hf
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], hs⟩

theorem field_scr (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) :
    (field L d).Disjoint L.SCR := hL.kc.sub_left (fieldWithin L hd).sub

theorem field_mem {m n : Mem} (hm : n = m) (d : Nat) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by rw [hm]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Equation`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def challenge (L : Lay) : Region := ⟨L.E+128,64⟩
def equationRd (L : Lay) : List Region := [L.PK,L.SIG,challenge L]
def equationWr (L : Lay) : List Region := [L.SCR]
def EqArgs (L : Lay) (s : State) : Prop := s.gpr .x0 = L.pk ∧
  s.gpr .x1 = L.sig ∧ s.gpr .x2 = L.E+128 ∧ s.gpr .x3 = L.scr

theorem equation_noFrames : verifyEquation.noFrames = true := by lit_decide

theorem challengeWithin (L : Lay) : Whole.Within (challenge L) L.FR :=
  ⟨128,rfl,by change 128+64≤256; decide⟩

theorem equation_pre (hL : L.Ok) (ha : EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (equationRd L) (equationWr L)) := by
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), ha.1,ha.2.1,ha.2.2.1,ha.2.2.2]
  exact ⟨rfl,rfl,hL.sc _ (by simp [Lay.inputs]),hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (challengeWithin L).sub,hL.nc⟩

theorem equation_covers : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [equationRd,equationWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inr ⟨L.PK,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inl (challengeWithin L)
  · exact .inr (scratch_covered L)

theorem equation_writes : ∀ r ∈ equationWr L,
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR,by simp [Lay.outputs],scratchWithin L⟩

theorem equation_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine Whole.call_ok hc verify_ok equation_noFrames (equation_pre hL ha)
    equation_covers equation_writes fun t ht _ hp => ⟨ht,?_⟩
  change t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x1) 64)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x2) 64)) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),ha.1,ha.2.1,ha.2.2.1] at hp
  exact hp

theorem equation_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith VG.Impl.Ed25519.AArch64.VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation) s
      fun t => Ctx L g v m₀ t ∧ t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [known]) (by simp [preserved]))
    fun u ⟨hu,hm,hav⟩ => ?_)
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  refine WP.mono (equation_call hu hL ⟨a0,a1,a2,a3⟩) fun t ⟨ht,hp⟩ => ⟨ht,?_⟩
  rw [hm] at hp
  exact hp

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.HashPipeline`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.HashInputs`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prefix_step (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {source count : Nat} (hsource : source < 5)
    (hcount : count < 65536) {prev : List Byte} (hp : prev.length = count)
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (prefixArgs source count)) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source) 32) := by
  apply update_ok backend hc hL ha (by simp)
    (by simp [Whole.valid]; omega) (by simp [known]; exact hsource) (by simp [preserved])
    (p := L.value source) (len := 32) (prev := prev) ?_ hd hi hr
  intro t hav
  have a0 := hav (.x0,.caller 4 0) (by simp)
  have a1 := hav (.x1,.const count) (by simp)
  have a2 := hav (.x2,.caller source 0) (by simp)
  have a3 := hav (.x3,.const 32) (by simp)
  have a4 := hav (.x4,.caller 4 192) (by simp)
  change t.gpr .x0 = L.scr + 0#64 at a0
  change t.gpr .x2 = L.value source + 0#64 at a2
  rw [BitVec.add_zero] at a0 a2
  exact ⟨a0, by rw [hp]; exact a1, a2, a3, a4⟩

theorem message_step (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {prev : List Byte} (hp : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix messageArgs) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem L.msg L.len.toNat) := by
  apply update_ok backend hc hL ha (by simp) (by simp [Whole.valid])
    (by simp [known]) (by decide) (p := L.msg) (len := L.len) (prev := prev) ?_
    (hL.sc _ (by simp [Lay.inputs])) ?_ hr
  · intro t hav
    have a0 := hav (.x0,.caller 4 0) (by simp)
    have a1 := hav (.x1,.const 64) (by simp)
    have a2 := hav (.x2,.caller 1 0) (by simp)
    have a3 := hav (.x3,.caller 2 0) (by simp)
    have a4 := hav (.x4,.caller 4 192) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    change t.gpr .x2 = L.msg + 0#64 at a2
    change t.gpr .x3 = L.len + 0#64 at a3
    rw [BitVec.add_zero] at a0 a2 a3
    exact ⟨a0, by rw [hp]; exact a1, a2, a3, a4⟩
  · exact ⟨L.MSG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.HashFinalize`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem finalize_writes : ∀ r ∈ Whole.finalizeWr L.scr (L.E+192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0+192≤8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192+64≤256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+688≤8192; decide⟩

theorem finalize_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {msg : List Byte}
    (hm : msg.length = 64 + L.len.toNat)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr msg) :
    WP isa (finalize backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E+192) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  unfold finalize VG.Impl.Ed25519.AArch64.Whole.callWith finalizeArgs
  apply WP.seq
  refine WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 4 0),(.x1,.caller 2 64),(.x2,.frame 192),(.x3,.caller 4 192)])
    (by decide) (by simp [Whole.valid]) (by simp [known]) (by decide)) ?_
  intro t ⟨ht, htmem, hav⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hav (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have a1 : t.gpr .x1 = BitVec.ofNat 64 msg.length := by
    have hh := hav (.x1,.caller 2 64) (by simp)
    change t.gpr .x1 = L.len + 64 at hh
    rw [hh, hm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_comm]
    rfl
  have a2 : t.gpr .x2 = L.E+192 := hav (.x2,.frame 192) (by simp)
  have a3 : t.gpr .x3 = L.scr+192 := hav (.x3,.caller 4 192) (by simp)
  have hd : Region.Disjoint ⟨L.E+192,64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide))
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr msg := htmem ▸ hr
  refine WP.mono (Whole.finalize_call backend ht (Whole.finalize_pre a0 a2 a3 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)))
    (Whole.covers_writes finalize_writes) finalize_writes a0 a2 a1 hr'
    (by rw [hm]; exact hL.message_bound)) fun u ⟨hu,_,hp⟩ => ⟨hu,hp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m L.sig 32 ++
    Spec.Ed25519.bytesAt m L.pk 32 ++
    Spec.Ed25519.bytesAt m L.msg L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : Ctx L g v m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem L.sig 32 = Spec.Ed25519.bytesAt m₀ L.sig 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm
    · exact (hL.ck _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem input_sig (hL : L.Ok) : Region.Disjoint ⟨L.value 3,32⟩ L.SCR ∧
    ∃ R ∈ L.inputs, Whole.Within ⟨L.value 3,32⟩ R := by
  refine ⟨(hL.sc L.SIG (by simp [Lay.inputs])).sub_left (Region.sub_prefix (by decide)),
    L.SIG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, ?_⟩
  change 0+32≤64
  decide

theorem input_pk (hL : L.Ok) : Region.Disjoint ⟨L.value 0,32⟩ L.SCR ∧
    ∃ R ∈ L.inputs, Whole.Within ⟨L.value 0,32⟩ R := by
  refine ⟨hL.sc L.PK (by simp [Lay.inputs]), L.PK, by simp [Lay.inputs], 0,
    (BitVec.add_zero _).symm, ?_⟩
  change 0+32≤32
  decide

theorem hash_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s)
    (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hash backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_ok hc hL ha) fun t ⟨ht,hinit⟩ => ?_)
  refine WP.seq (WP.mono (prefix_step backend ht hL ha (source := 3) (count := 0)
    (by decide) (by decide) rfl (input_sig hL).1 (input_sig hL).2 hinit)
    fun u ⟨hu,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem L.sig 32) at hsig
  rw [List.nil_append, sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (prefix_step backend hu hL ha (source := 0) (count := 32)
    (by decide) (by decide) (bytes_length _ _ _) (input_pk hL).1 (input_pk hL).2 hsig)
    fun w ⟨hw,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem L.pk 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ L.sig 32 ++ Spec.Ed25519.bytesAt m₀ L.pk 32).length = 64 := by
    rw [List.length_append, bytes_length, bytes_length]
  refine WP.seq (WP.mono (message_step backend hw hL ha hpkl hpk) fun z ⟨hz,hmsg⟩ => ?_)
  rw [hw.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat≤2^64; omega)] at hmsg
  have hlen : (hashInput L m₀).length = 64 + L.len.toNat := by
    simp only [hashInput, List.length_append, bytes_length]
  exact finalize_ok backend hz hL ha hlen hmsg

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.Reduce`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
open VG.Impl.Ed25519.AArch64 (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .x0 = L.E + BitVec.ofNat 64 d ∧ s.gpr .x1 = L.E + 192 ∧ s.gpr .x2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, hL.kc.sub_left (digestWithin L).sub⟩

theorem reduce_call (hc : Ctx L g v m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g v m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratchWithin L)
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarReduceLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem reduce_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) s
      fun t => Ctx L g v m₀ t ∧ Frame (reduceWr L 128) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .frame 128), (.x1, .frame 192), (.x2, .caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [known]) (by simp [preserved]))
    fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .frame 128) (by simp)
  have a1 := hs (.x1, .frame 192) (by simp)
  have a2 := hs (.x2, .caller 4 0) (by simp)
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL (d := 128) (by decide) ⟨a0,a1,a2⟩)
    fun t ⟨ht,hf,hp⟩ => ⟨ht,?_,?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduced_challenge (digest : List Byte) :
    Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) =
      Spec.Ed25519.scalarReduce digest ++ Spec.Ed25519.encodeLE 32 0 := by
  simp only [Spec.Ed25519.scalarReduce, Proof.Ed25519.AArch64.encodeLE_eq]
  rw [show (64 : Nat) = 32 + 32 from rfl, Proof.X25519.leBytes_add]
  have hL : Spec.Ed25519.L ≤ 256 ^ 32 := by decide
  have hpos : 0 < Spec.Ed25519.L := by decide
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hL)]

theorem extend_step (hc : Ctx L g v m₀ s) {digest : List Byte}
    (hd : Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 = Spec.Ed25519.scalarReduce digest) :
    WP isa (.block extendChallenge) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 128) 64 =
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L) := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 20) (count := 4) (by decide)) fun t ⟨ht, hf, hz⟩ => ⟨ht, ?_⟩
  have low : Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E + 128) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (R := ⟨L.E + 128, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  have high : Spec.Ed25519.bytesAt t.mem (L.E + 160) 32 = Spec.Ed25519.encodeLE 32 0 := by
    rw [Proof.Ed25519.AArch64.encodeLE_eq]
    have word (j : Nat) (hj : j < 4) : t.mem.readW (L.E + 160 + BitVec.ofNat 64 (8*j)) 64 = 0 := by
      have z := hz j hj
      have e : L.E + BitVec.ofNat 64 (8*(20+j)) = L.E + 160 + BitVec.ofNat 64 (8*j) := by
        rw [show 8*(20+j)=160+8*j by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [e] at z
      exact z
    apply Proof.X25519.bytesAt_leBytes_words64
    · have z := word 0 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 1 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 2 (by decide)
      simpa using congrArg BitVec.toNat z
    · have z := word 3 (by decide)
      simpa using congrArg BitVec.toNat z
  change Spec.X25519.bytesAt t.mem (L.E + 128) (32 + 32) = _
  rw [Proof.X25519.bytesAt_add]
  change Spec.Ed25519.bytesAt t.mem (L.E + 128) 32 ++
    Spec.Ed25519.bytesAt t.mem (L.E + 128 + 32) 32 = _
  rw [show L.E + 128 + 32 = L.E + 160 by rw [BitVec.add_assoc]; rfl,
    low, hd, high, reduced_challenge]

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hashInput_eq (L : Lay) (m : Mem) : hashInput L m =
    (Spec.Ed25519.bytesAt m L.sig 64).take 32 ++
      Spec.Ed25519.bytesAt m L.pk 32 ++
      Spec.Ed25519.bytesAt m L.msg L.len.toNat := by
  have e : (Spec.Ed25519.bytesAt m L.sig 64).take 32 =
      Spec.Ed25519.bytesAt m L.sig 32 := by
    unfold Spec.Ed25519.bytesAt
    rw [← List.map_take, List.take_range]
    rfl
  rw [e]
  rfl

theorem body_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) :
    WP isa (body backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verify (Spec.Ed25519.bytesAt m₀ L.pk 32)
        (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) (Spec.Ed25519.bytesAt m₀ L.sig 64)) := by
  refine WP.seq (WP.mono (hash_ok backend hc hL ha) fun t ⟨ht,hh⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step ht hL ha) fun u ⟨hu,_,hr⟩ => ?_)
  rw [hh] at hr
  refine WP.seq (WP.mono (extend_step hu hr) fun w ⟨hw,he⟩ => ?_)
  rw [hashInput_eq] at he
  refine WP.mono (equation_step hw hL ha) fun z ⟨hz,eq⟩ => ⟨hz,?_⟩
  rw [hw.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide),
    hw.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64≤2^64; decide),he] at eq
  exact eq

theorem body_depth (backend : Whole.Backend) : (body backend.code backend.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth backend
  have hf := Whole.finalize_depth backend
  change (Impl.Sha512.AArch64.Stream.updateWith backend.suffix backend.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith backend.suffix backend.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames reduce_noFrames
  have he := Whole.depth_zero_of_noFrames equation_noFrames
  simp only [body,Impl.Ed25519.AArch64.VerifyMessage.hash,init,update,finalize,Impl.Ed25519.AArch64.Whole.callWith,
    Code.aarch64Depth,Impl.Sha512.AArch64.Stream.init,hr,he]
  omega

end VG.Proof.Ed25519.AArch64.VerifyMessage
