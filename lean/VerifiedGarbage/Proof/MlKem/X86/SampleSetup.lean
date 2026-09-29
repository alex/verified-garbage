import VerifiedGarbage.Proof.MlKem.X86.Keccak
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.MlKem.Sample
import VerifiedGarbage.Impl.MlKem.X86.Sample
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): the SHAKE128 output of `vg_mlkem_sample_ntt`

Untrusted: everything here is checked by Lean. `vg_mlkem_sample_ntt(seed,
a, scratch)` loads `scratch` into `esi` (`ld_piece`), zeros the Keccak state
at `scratch + 840` (`zero_piece`), and absorbs the 34 bytes of the seed,
pads, and squeezes 840 bytes into `scratch` with the verified Keccak
functions (`absorb_call`, `pad_call`, `squeeze_call`), leaving the first 840
bytes of the XOF output of the seed there (`Out`).

The state `Base` is what holds throughout the body: `esp` as the leaf's
frame left it, the permissions, and memory changed only in `a`, `scratch`
and the 40 bytes of stack below the frame that the calls use (`W`).
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr)

section
variable (s₀ : State)
abbrev dP : BitVec 32 := arg s₀ 0
abbrev aP : BitVec 32 := arg s₀ 1
abbrev sP : BitVec 32 := arg s₀ 2
abbrev dA : Addr := (dP s₀).setWidth 64
abbrev aA : Addr := (aP s₀).setWidth 64
abbrev sA : Addr := (sP s₀).setWidth 64
abbrev dR : Region := ⟨dA s₀, 34⟩
abbrev sR : Region := ⟨sA s₀, 2048⟩
abbrev gR : Region := ⟨argAddr s₀ 0, 12⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 56#64, 56⟩
/-- The seed. -/
abbrev Bs : List Byte := bytesAt s₀.mem (dA s₀) 34
/-- `esp` in the body. -/
abbrev E1 : BitVec 32 := (P0 s₀).gpr .esp
/-- The stack the calls use. -/
abbrev cR : Region := below (E1 s₀) 40
/-- The Keccak state. -/
abbrev SS : BitVec 32 := sP s₀ + BitVec.ofNat 32 840
/-- The Keccak functions' working space. -/
abbrev WW : BitVec 32 := sP s₀ + BitVec.ofNat 32 1040
/-- What the body may change. -/
abbrev W : List Region := [polyRegion (aA s₀), sR s₀, cR s₀]
end

structure Pre (s₀ : State) : Prop where
  sp : 56 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [polyRegion (aA s₀), sR s₀, gR s₀]
  d_a : (dR s₀).Disjoint (polyRegion (aA s₀))
  d_s : (dR s₀).Disjoint (sR s₀)
  d_g : (dR s₀).Disjoint (gR s₀)
  a_s : (polyRegion (aA s₀)).Disjoint (sR s₀)
  a_g : (polyRegion (aA s₀)).Disjoint (gR s₀)
  s_g : (sR s₀).Disjoint (gR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_a : (retR s₀).Disjoint (polyRegion (aA s₀))
  ret_s : (retR s₀).Disjoint (sR s₀)
  ret_g : (retR s₀).Disjoint (gR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_a : (stkR s₀).Disjoint (polyRegion (aA s₀))
  stk_s : (stkR s₀).Disjoint (sR s₀)
  stk_g : (stkR s₀).Disjoint (gR s₀)
  d_fit : (dP s₀).toNat + 34 ≤ 2 ^ 32
  a_fit : (aP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (sP s₀).toNat + 2048 ≤ 2 ^ 32

theorem Pre.of {s₀ : State} (h : (sampleNTTContract X86.abi 56).pre s₀) : Pre s₀ := by
  sig_pre [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-- The pointers, `esp` and the seed agree. -/
def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ Bs s₀ = Bs s₀' ∧ dP s₀ = dP s₀' ∧ aP s₀ = aP s₀' ∧ sP s₀ = sP s₀'

theorem Pub.E1 {s₀ s₀' : State} (hq : Pub s₀ s₀') : E1 s₀ = E1 s₀' := by
  simp only [P0_esp, hq.1]

/-! ## Regions -/

/-- The `a` bytes below `sp` and the `b` bytes below them. -/
theorem below_adj {sp : BitVec 32} {a b : Nat} (h : a + b ≤ sp.toNat) :
    (below sp a).Disjoint (below (sp - BitVec.ofNat 32 a) b) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hk : b ≤ (sp - BitVec.ofNat 32 a).toNat := by rw [sub_toNat (by omega)]; omega
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [Taint.sub_setWidth hk, Taint.sub_setWidth (by omega)] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

/-- The return address and the stack below it. -/
theorem ret_below {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    (⟨sp.setWidth 64, 4⟩ : Region).Disjoint (below sp n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth h] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

/-- Two parts of a region at a 32-bit pointer that do not overlap. -/
theorem disj_at {x : BitVec 32} {len a b n k : Nat} (ha : a + n ≤ len) (hb : b + k ≤ len)
    (hx : x.toNat + len ≤ 2 ^ 32) (h : a + n ≤ b ∨ b + k ≤ a) :
    (⟨x.setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 b, k⟩ :=
  fun y h₁ h₂ => sep_at ha hb hx h y (by simp only [Region.Contains] at h₁; omega)
    (by simp only [Region.Contains] at h₂; omega)

theorem toNat_off {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

theorem esp_nat (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) : (E1 s₀).toNat = (E0 s₀).toNat - 16 := by
  rw [E1, P0_esp]; exact sub_toNat (k := 16) h

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_below : stkR s₀ = below (E0 s₀) 56 := by
  simp only [stkR, below]; rw [Taint.sub_setWidth hp.sp]

theorem frame_sub : Region.Sub (frameR s₀) (stkR s₀) := by
  rw [hp.stk_below]; exact below_sub (by omega) hp.sp

omit hp in
theorem cR_eq : cR s₀ = below (E0 s₀ - BitVec.ofNat 32 16) 40 := by
  show below ((P0 s₀).gpr .esp) 40 = _
  rw [P0_esp]; rfl

theorem c_sub : Region.Sub (cR s₀) (stkR s₀) := by
  rw [hp.stk_below, cR_eq]
  exact below_inner (sp := E0 s₀) (a := 40) (b := 56) (k := 16) (by omega) hp.sp

theorem frame_c : (frameR s₀).Disjoint (cR s₀) := cR_eq (s₀ := s₀) ▸ below_adj (sp := E0 s₀) (a := 16) (b := 40) (by have := hp.sp; omega)

theorem ret_c : (retR s₀).Disjoint (cR s₀) :=
  (hp.stk_below ▸ ret_below (sp := E0 s₀) hp.sp).sub_right hp.c_sub

theorem fr16 : (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth (by have := hp.sp; omega)]

theorem hW : ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨hp.stk_a.sub_left hp.frame_sub, hp.ret_a⟩
  · exact ⟨hp.stk_s.sub_left hp.frame_sub, hp.ret_s⟩
  · exact ⟨hp.frame_c, hp.ret_c⟩

theorem dW : ∀ r ∈ W s₀, (dR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.d_a
  · exact hp.d_s
  · exact (hp.stk_d.sub_left hp.c_sub).symm

theorem gW : ∀ r ∈ W s₀, (gR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_g.symm
  · exact hp.s_g.symm
  · exact (hp.stk_g.sub_left hp.c_sub).symm

theorem sub_s {o n : Nat} (h : o + n ≤ 2048) : Region.Sub ⟨sA s₀ + BitVec.ofNat 64 o, n⟩ (sR s₀) :=
  sub_of_contains (contains_at h hp.s_fit)

theorem off_eq {o : Nat} (h : o < 2048) : (sP s₀ + BitVec.ofNat 32 o).setWidth 64 = sA s₀ + BitVec.ofNat 64 o :=
  ea_off (by have := hp.s_fit; omega)

theorem reg_s {o n : Nat} (h : o < 2048) :
    reg32 (sP s₀ + BitVec.ofNat 32 o) n = ⟨sA s₀ + BitVec.ofNat 64 o, n⟩ := by
  show (⟨(sP s₀ + BitVec.ofNat 32 o).setWidth 64, n⟩ : Region) = _
  rw [hp.off_eq h]

omit hp in
theorem reg_s0 {n : Nat} : reg32 (sP s₀) n = ⟨sA s₀ + BitVec.ofNat 64 0, n⟩ := by
  show (⟨(sP s₀).setWidth 64, n⟩ : Region) = _
  simp only [BitVec.add_zero]

/-- The push changes nothing but the frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact Nat.le_trans (by decide) hp.sp)
  rw [saveRegs_len] at hf
  exact hf

theorem seed0 : bytesAt (P0 s₀).mem (dA s₀) 34 = Bs s₀ :=
  bytesAt_frame hp.P0_keep (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.stk_d.sub_left hp.frame_sub).symm) (by decide)

theorem kbufs : KBufs (E1 s₀) (SS s₀) (WW s₀) := by
  have hs := hp.s_fit
  have e := esp_nat s₀ (by have := hp.sp; omega)
  have hsp := hp.sp
  refine ⟨by rw [e]; omega, by rw [toNat_off (by omega)]; omega, by rw [toNat_off (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [hp.reg_s (by omega), hp.reg_s (by omega)]
    exact disj_at (len := 2048) (by omega) (by omega) hs (by omega)
  · rw [hp.reg_s (by omega)]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · rw [hp.reg_s (by omega)]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))

theorem within_s {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (ho : o < 2048) (h : o + n ≤ 2048) :
    Within (reg32 (sP s₀ + BitVec.ofNat 32 o) n) s.wr := by
  rw [hp.reg_s ho]
  exact ⟨sR s₀, by rw [hw, P0_wr, hp.wr]; simp, o, rfl, h⟩

theorem within_s0 {s : State} (hw : s.wr = (P0 s₀).wr) {n : Nat} (h : n ≤ 2048) :
    Within (reg32 (sP s₀) n) s.wr := by
  rw [Pre.reg_s0]
  exact ⟨sR s₀, by rw [hw, P0_wr, hp.wr]; simp, 0, rfl, by simpa using h⟩

end Pre

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = E1 s₀
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (W s₀) (P0 s₀).mem s.mem

/-- `Base`, with `esi = scratch`. -/
structure Ctx (s₀ s : State) : Prop extends Base s₀ s where
  esi : s.gpr .esi = sP s₀

namespace Base
variable {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s)
include hp h

theorem seed : bytesAt s.mem (dA s₀) 34 = Bs s₀ :=
  (bytesAt_frame h.frame hp.dW (by decide)).trans hp.seed0

theorem argw {i : Nat} (hi : i < 3) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have fit := hp.sp'
  rw [h.frame.readW (arg_contains (n := 3) hi fit) hp.gW (by decide)]
  exact P0_arg (by have := hp.sp; omega) hi fit (by rw [hp.fr16]; exact (hp.stk_g.sub_left hp.frame_sub))

theorem argIn {i : Nat} (hi : i < 3) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [h.rd, h.wr]
  exact P0_argIn hi hp.sp' (by simp [hp.wr])

omit hp in
theorem argEa {i : Nat} : (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h.esp]; exact P0_argAddr s₀ i

omit hp in
/-- After a call that changes memory only within `rs`, parts of `W`. -/
theorem call {s' : State} (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ W s₀, Region.Sub r r') : Base s₀ s' :=
  ⟨by rw [e₃ .esp (by simp [calleeSaved]), h.esp], by rw [e₁, h.rd], by rw [e₂, h.wr],
    h.frame.trans (fr.sub hs)⟩

end Base

theorem Ctx.call {s₀ s s' : State} (h : Ctx s₀ s) (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ W s₀, Region.Sub r r') : Ctx s₀ s' :=
  ⟨h.toBase.call e₁ e₂ e₃ fr hs, by rw [e₃ .esi (by simp [calleeSaved]), h.esi]⟩

/-- The regions a call of the Keccak functions changes are parts of `W`. -/
theorem calls_sub {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [reg32 (SS s₀) 200, reg32 (sP s₀) 840, reg32 (WW s₀) 640, below (E1 s₀) 40],
      ∃ r' ∈ W s₀, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by omega)⟩
  · exact ⟨sR s₀, by simp, by rw [Pre.reg_s0]; exact hp.sub_s (by omega)⟩
  · exact ⟨sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by omega)⟩
  · exact ⟨cR s₀, by simp, fun _ h => h⟩

theorem calls_sub3 {s₀ : State} (hp : Pre s₀) :
    ∀ r ∈ [reg32 (SS s₀) 200, reg32 (WW s₀) 640, below (E1 s₀) 40], ∃ r' ∈ W s₀, Region.Sub r r' :=
  fun r hr => calls_sub hp r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h])

/-! ## `esi = scratch` -/

theorem ld_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Ctx (.block [.mov .esi (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have b₀ : Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a₂ := b₀.argEa (i := 2)
    have i₂ := b₀.argIn hp (i := 2) (by omega)
    have v₂ := b₀.argw hp (i := 2) (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₂
    apply WP.of_runBlock
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₂, i₂, v₂, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨⟨by simp, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-! ## The Keccak state set to zero -/

/-- After `k` words. -/
structure ZInv (s₀ : State) (k : Nat) (s : State) : Prop extends Ctx s₀ s where
  ebx : s.gpr .ebx = SS s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (50 - k)
  eax : s.gpr .eax = 0
  zero : ∀ j < 4 * k, s.mem ((SS s₀).setWidth 64 + BitVec.ofNat 64 j) = 0

theorem zinit_piece : Piece Pre Pub Ctx (ZInv · 0) (.block (zeroInit smpSt)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [zeroInit, smpSt, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, by simp [h.esi], by simp, by simp,
    fun j hj => absurd hj (by omega)⟩

theorem zero_write {m : Mem} {a : Addr} {k : Nat}
    (h : ∀ j < 4 * k, m (a + BitVec.ofNat 64 j) = 0) :
    ∀ j < 4 * (k + 1), (m.writeW (a + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32)) (a + BitVec.ofNat 64 j) = 0 := by
  intro j hj
  simp only [Mem.writeW, Mem.write]
  split
  · simp
  · rename_i hn
    refine h j (Nat.lt_of_not_le fun hc => hn ?_)
    rw [show a + BitVec.ofNat 64 j - (a + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 (j - 4 * k) by
      rw [show j = 4 * k + (j - 4 * k) by omega, BitVec.ofNat_add]; bv_omega]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

theorem zstep {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 50) {s : State} (h : ZInv s₀ k s) :
    WP isa (.block zeroBody) s fun s' => ZInv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 50)) := by
  have hs := hp.s_fit
  have tS : (SS s₀).toNat = (sP s₀).toNat + 840 := toNat_off (by omega)
  have ea : (SS s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 =
      (SS s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) := by
    rw [ea_add (by omega)]; rfl
  have eS : (SS s₀).setWidth 64 = sA s₀ + BitVec.ofNat 64 840 := hp.off_eq (by omega)
  have hin : InRegions s.wr ((SS s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [eS, BitVec.add_assoc, ← BitVec.ofNat_add, h.wr, P0_wr, hp.wr]
    exact ⟨sR s₀, by simp, contains_at (by omega) hs⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [zeroBody, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, h.ebx, ea, hin, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, ?_⟩, by simp [h.esi]⟩, ?_, ?_, by simp [h.eax], ?_⟩, ?_⟩
  · refine h.frame.writeW (r := sR s₀) (by simp) _ ?_
    rw [eS, BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_at (by omega) hs
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [h.eax]; exact zero_write h.zero
  · simp only [eval, h.ecx]
    exact cnt_ne hk (by omega)

theorem zloop_piece : Piece Pre Pub (ZInv · 0) (ZInv · 50) (.loop (.block zeroBody) .ne) :=
  Piece.countLoop (by decide) (fun k s₀ s => ZInv s₀ k s) [.ebx]
    (fun k hk s₀ s hp h => zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ebx, h'.ebx, SS, SS, hq.2.2.2.2]) (by taint_decide)

theorem stateAt_zero {m : Mem} {p : Addr} (h : ∀ j < 200, m (p + BitVec.ofNat 64 j) = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [Mem.readW_congr (m' := fun _ => 0) fun b hb => ?_]
  · simp [Mem.readW, Mem.read]
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)

/-- `Ctx`, with the Keccak state zero. -/
structure Z (s₀ s : State) : Prop extends Ctx s₀ s where
  st : stateAt s.mem ((SS s₀).setWidth 64) = Spec.Sha3.zero

theorem zero_piece : Piece Pre Pub Ctx Z (zeroSt smpSt) :=
  (Piece.seq zinit_piece zloop_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨h.toCtx, stateAt_zero fun j hj => h.zero j (by omega)⟩

end VG.Proof.MlKem.X86.Sample
