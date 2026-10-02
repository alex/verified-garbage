import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.Variant
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract

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
