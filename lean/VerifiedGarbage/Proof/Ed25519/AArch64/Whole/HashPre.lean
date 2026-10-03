import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.Variant
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract

/-! Merged from `Proof.Ed25519.AArch64.Whole.Hash`. -/
section
/-! SHA-512 calls parameterized by the verified compression backend. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64
open VG.Impl.Sha512.AArch64.Stream (init)

abbrev Backend := Proof.Sha512.AArch64.Compress

theorem update_depth (v : Backend) : v.update.aarch64Depth ≤ 1 := Nat.le_of_eq v.update_depth

theorem finalize_depth (v : Backend) : v.finalize.aarch64Depth ≤ 1 := Nat.le_of_eq v.finalize_depth

variable {E : Addr} {g : Reg → BitVec 64} {vec : VReg → BitVec 128}
  {m₀ : Mem} {rd wr : List Region} {t : State}

theorem init_call (hc : Ctx E g vec m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : (Proof.Sha512.initAArch64 Spec.Sha512.H0_512).pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr : Addr} (ha : t.gpr .x0 = scr) :
    WP isa (.call Spec.Sha512.init512Api.name (init Spec.Sha512.H0_512)) t fun u =>
      Ctx E g vec m₀ rd wr u ∧ Frame wr' t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem scr [] := by
  refine call_ok hc (Proof.Sha512.AArch64.Stream.init_verified _).1 rfl hp hcov hw
    fun u hu hf hpost => ⟨hu, hf, ?_⟩
  change Spec.Sha512.Repr _ u.mem (t.callEntry.gpr .x0) [] at hpost
  rw [State.callEntry_gpr _ (by decide), ha] at hpost
  exact hpost

theorem update_call (v : Backend) (hc : Ctx E g vec m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.updateAArch64.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr p len : Addr} {prev : List Byte}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = p) (h3 : t.gpr .x3 = len)
    (hcount : t.gpr .x1 = BitVec.ofNat 64 prev.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem scr prev) :
    WP isa (.call (Spec.Sha512.updateApi.name ++ v.suffix) v.update) t fun u =>
      Ctx E g vec m₀ rd wr u ∧ Frame (wr' ++ [CK E]) t.mem u.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem scr
        (prev ++ Spec.Ed25519.bytesAt t.mem p len.toNat) := by
  refine call_okF hc v.update_verified.1 (update_depth v) hp hcov hw
    fun u hu hf hpost => ⟨hu, hf, ?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .x0 = scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h0]
  have h1' : (t.callEntry.withRegions rd' wr').gpr .x1 = BitVec.ofNat 64 prev.length := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hcount]
  have hh := hpost Spec.Sha512.H0_512 prev (by rw [h0']; exact hr) h1'
  change Spec.Sha512.Repr _ u.mem (t.callEntry.gpr .x0)
    (prev ++ Spec.Ed25519.bytesAt t.mem (t.callEntry.gpr .x2) (t.callEntry.gpr .x3).toNat) at hh
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h2, h3] at hh
  exact hh

theorem finalize_call (v : Backend) (hc : Ctx E g vec m₀ rd wr t)
    {rd' wr' : List Region}
    (hp : Proof.Sha512.finalizeAArch64.pre (t.callEntry.withRegions rd' wr'))
    (hcov : Covers (rd' ++ wr') (rd ++ FR E :: wr))
    (hw : ∀ r ∈ wr', Within r (FR E) ∨ ∃ R ∈ wr, Within r R)
    {scr out : Addr} {msg : List Byte}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = out)
    (hcount : t.gpr .x1 = BitVec.ofNat 64 msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem scr msg) (hlen : msg.length < 2 ^ 64) :
    WP isa (.call (Spec.Sha512.finalizeApi.name ++ v.suffix) v.finalize) t fun u =>
      Ctx E g vec m₀ rd wr u ∧ Frame (wr' ++ [CK E]) t.mem u.mem ∧
      Spec.Ed25519.bytesAt u.mem out 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  refine call_okF hc v.finalize_verified.1 (finalize_depth v) hp hcov hw
    fun u hu hf hpost => ⟨hu, hf, ?_⟩
  have h0' : (t.callEntry.withRegions rd' wr').gpr .x0 = scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), h0]
  have h1' : (t.callEntry.withRegions rd' wr').gpr .x1 = BitVec.ofNat 64 msg.length := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hcount]
  have hh := hpost Spec.Sha512.H0_512 msg (by rw [h0']; exact hr) hlen h1'
  change Spec.Ed25519.bytesAt u.mem (t.callEntry.gpr .x2) 64 = _ at hh
  rw [State.callEntry_gpr _ (by decide), h2] at hh
  exact hh

end VG.Proof.Ed25519.AArch64.Whole
end

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

abbrev SHA (scr : Addr) : Region := ⟨scr, 192⟩
abbrev WORK (scr : Addr) : Region := ⟨scr + 192, 688⟩
def initWr (scr : Addr) : List Region := [SHA scr]
def updateRd (p len : Addr) : List Region := [⟨p, len.toNat⟩]
def hashWr (scr : Addr) : List Region := [SHA scr, WORK scr]
def finalizeWr (scr out : Addr) : List Region := [SHA scr, ⟨out, 64⟩, WORK scr]

theorem sha_sub (scr : Addr) : Region.Sub (SHA scr) ⟨scr, 8192⟩ := Region.sub_prefix (by decide)
theorem work_sub (scr : Addr) : Region.Sub (WORK scr) ⟨scr, 8192⟩ :=
  Offset.sub_base _ (by decide)
theorem sha_work (scr : Addr) : (SHA scr).Disjoint (WORK scr) :=
  Offset.base_disjoint _ (by decide) (by decide)

theorem init_pre {t : State} {scr : Addr} (ha : t.gpr .x0 = scr) :
    (Proof.Sha512.initAArch64 Spec.Sha512.H0_512).pre
      (t.callEntry.withRegions [] (initWr scr)) := by
  simp only [Proof.Sha512.initAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), ha]
  exact ⟨True.intro, rfl⟩

theorem update_pre {t : State} {scr p len : Addr}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = p) (h3 : t.gpr .x3 = len)
    (h4 : t.gpr .x4 = scr + 192)
    (hd : Region.Disjoint ⟨p, len.toNat⟩ ⟨scr, 8192⟩) (hsp : 16 ≤ t.sp.toNat)
    (hks : (CK t.sp).Disjoint ⟨scr, 8192⟩) (hkp : (CK t.sp).Disjoint ⟨p, len.toNat⟩) :
    Proof.Sha512.updateAArch64.pre
      (t.callEntry.withRegions (updateRd p len) (hashWr scr)) := by
  simp only [Proof.Sha512.updateAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h2, h3, h4]
  exact ⟨rfl, rfl, sha_work scr, hd.sub_right (sha_sub scr), hd.sub_right (work_sub scr), hsp,
    hks.sub_right (sha_sub scr), hkp, hks.sub_right (work_sub scr)⟩

theorem finalize_pre {t : State} {scr out : Addr}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = out) (h3 : t.gpr .x3 = scr + 192)
    (hd : Region.Disjoint ⟨out, 64⟩ ⟨scr, 8192⟩) (hsp : 16 ≤ t.sp.toNat)
    (hks : (CK t.sp).Disjoint ⟨scr, 8192⟩) (hko : (CK t.sp).Disjoint ⟨out, 64⟩) :
    Proof.Sha512.finalizeAArch64.pre
      (t.callEntry.withRegions [] (finalizeWr scr out)) := by
  simp only [Proof.Sha512.finalizeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h2, h3]
  exact ⟨True.intro, rfl, (hd.sub_right (sha_sub scr)).symm, sha_work scr, hd.sub_right (work_sub scr), hsp,
    hks.sub_right (sha_sub scr), hko, hks.sub_right (work_sub scr)⟩

/-- The SHA state and temporary workspace are prefixes of the outer scratch. -/
theorem hash_writes {E scr : Addr} {wr : List Region} (hs : (⟨scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ hashWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  simp only [hashWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, hs, 0, (BitVec.add_zero scr).symm, by change 0+192≤8192; decide⟩
  · exact .inr ⟨_, hs, 192, rfl, by change 192+688≤8192; decide⟩

theorem init_writes {E scr : Addr} {wr : List Region} (hs : (⟨scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ initWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  simp only [initWr, List.mem_singleton] at hr
  subst r
  exact .inr ⟨_, hs, 0, (BitVec.add_zero scr).symm, by change 0+192≤8192; decide⟩

theorem covers_writes {E : Addr} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, Within r (FR E) ∨ ∃ R ∈ wr, Within r R) :
    Covers ws (rd ++ FR E :: wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_right _ (List.mem_cons_of_mem _ hR), hs⟩

end VG.Proof.Ed25519.AArch64.Whole
