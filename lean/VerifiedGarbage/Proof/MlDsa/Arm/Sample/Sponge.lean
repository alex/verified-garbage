import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Common
import VerifiedGarbage.Proof.MlKem.Arm.Sample
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.Sample.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# ML-DSA on 32-bit ARM: the sampling functions' SHAKE

What the sampling functions share (`Impl/MlDsa/Arm/Sample/Common.lean`), for
any of them: a call is described by `Sp` (the message, its length, the working
space `scratch`, the output polynomial and the parameter), whose regions are
laid out as `SpOk` says of the entry state. From the prologue on, `Env` holds:
`r5` is the output polynomial and `r6` the working space, our caller's
`r4`–`r11` and `lr` are saved at `scratch + 2012`, and the memory has changed
only in the output polynomial, the working space and the 8 bytes below the
stack pointer. `sponge` then leaves `outlen` bytes of SHAKE of the message at
`scratch + 840` (`sponge_ok`, from `J0` to `J6`), and two runs of it from
calls that agree leak the same (`sponge_ct`).
-/

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)
open VG.Proof.MlKem.Arm.Sample (Regs regs_cs zeroWords_ok stateAt_zero fit_add)
open VG.Impl.MlDsa.Arm.Sample
open VG.Impl.MlKem.Arm (absorbCall padCall squeezeCall zeroState savedRegs)
open VG.Spec.Sha3 (bytesAt stateAt rates squeezeFrom)
open VG.Proof.MlDsa.Sample (padded polyR)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : BitVec 32
  len : Nat
  /-- `scratch`. -/
  scr : BitVec 32
  /-- The output polynomial. -/
  a : BitVec 32
  /-- The parameter, in `r7`. -/
  prm : BitVec 32

namespace Sp
variable (P : Sp)
/-- `scratch`, as an address. -/
abbrev S : Addr := State.addr P.scr
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.S + BitVec.ofNat 64 off
/-- The output polynomial, as an address. -/
abbrev A : Addr := State.addr P.a
abbrev scrR : Region := ⟨P.S, 2048⟩
abbrev sdR : Region := ⟨State.addr P.sd, P.len⟩
abbrev aR : Region := polyR P.A
/-- The message. -/
abbrev msg (σ : State) : List Byte := bytesAt σ.mem (State.addr P.sd) P.len
end Sp

/-- The regions of a call, from the entry state `σ`. -/
structure SpOk (P : Sp) (σ : State) : Prop where
  rd : P.sdR ∈ σ.rd
  wr : σ.wr = [P.aR, P.scrR]
  sd_a : P.sdR.Disjoint P.aR
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : P.aR.Disjoint P.scrR
  b_sd : (below σ 8).Disjoint P.sdR
  b_a : (below σ 8).Disjoint P.aR
  b_scr : (below σ 8).Disjoint P.scrR
  fsd : P.sd.toNat + P.len ≤ 2 ^ 32
  len_lt : P.len < 2 ^ 32
  fa : P.a.toNat + 1024 ≤ 2 ^ 32
  fscr : P.scr.toNat + 2048 ≤ 2 ^ 32
  sp8 : 8 ≤ σ.sp.toNat

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  r5 : s.gpr .r5 = P.a
  r6 : s.gpr .r6 = P.scr
  sav : Saved s.mem (P.at' 2012) σ.gpr
  savlr : s.mem.readW (P.at' 2044) 32 = σ.gpr .lr
  frame : Frame [P.aR, P.scrR, below σ 8] σ.mem s.mem

/-- Where a piece of code may write, keeping `Env`: the working space below
the saved registers, the output polynomial and the 8 bytes below the stack
pointer. -/
def Sp.Wr (P : Sp) (σ : State) (r : Region) : Prop :=
  Region.Sub r ⟨P.S, 2012⟩ ∨ Region.Sub r P.aR ∨ Region.Sub r (below σ 8)

theorem below_eq {σ s : State} (h : s.sp = σ.sp) : below s 8 = below σ 8 := by simp only [below, h]

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- A 32-bit address in the working space. -/
theorem at_eq {k : Nat} (hk : k < 2048) : State.addr (P.scr + BitVec.ofNat 32 k) = P.at' k :=
  addr_add (by have := hp.fscr; omega)

theorem regA_at {k : Nat} (hk : k < 2048) (n : Nat) : regA (P.scr + BitVec.ofNat 32 k) n = ⟨P.at' k, n⟩ := by
  simp only [regA, at_eq hp hk]

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

omit hp in
theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨P.S, n⟩ P.scrR := Region.sub_prefix h

theorem inScr {s : State} (he : Env P σ s) {a n : Nat} (h : a + n ≤ 2048) : InRegions s.wr (P.at' a) n := by
  rw [he.wr, hp.wr]
  exact ⟨P.scrR, by simp, Offset.contains_base _ h (by omega)⟩

theorem inScrRd {s : State} (he : Env P σ s) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  obtain ⟨r, hr, hc⟩ := inScr hp he h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Regions at offsets of the working space are within the writable regions. -/
theorem covScr {s : State} (he : Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.S + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [he.wr, hp.wr]; simp, off, hb, hl⟩

theorem covScrRd {s : State} (he : Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.S + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers rs (s.rd ++ s.wr) := fun x n hi => by
  obtain ⟨r, hr, hc⟩ := covScr hp he h x n hi
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The saved registers are apart from where code may write. -/
theorem sav_disj {r : Region} (h : P.Wr σ r) : (⟨P.at' 2012, 36⟩ : Region).Disjoint r := by
  rcases h with h | h | h
  · exact (Offset.disjoint_base P.S (d := 2012) (n := 36) (k := 2012) (Nat.le_refl _) (by omega)).sub_right h
  · exact (hp.a_scr.sub_right (sub_scr (a := 2012) (n := 36) (by omega))).symm.sub_right h
  · exact (hp.b_scr.sub_right (sub_scr (a := 2012) (n := 36) (by omega))).symm.sub_right h

/-- `Env` after writes where code may write. -/
theorem Env.step {s s' : State} (he : Env P σ s) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hrs : ∀ r ∈ rs, P.Wr σ r) (g5 : s'.gpr .r5 = s.gpr .r5) (g6 : s'.gpr .r6 = s.gpr .r6)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Env P σ s' := by
  refine ⟨rd.trans he.rd, wr.trans he.wr, sp.trans he.sp, g5.trans he.r5, g6.trans he.r6, fun i hi => ?_, ?_, ?_⟩
  · rw [hf.readW (r := ⟨P.at' 2012, 36⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => sav_disj hp (hrs r hr)) (by decide)]
    exact he.sav i hi
  · rw [hf.readW (r := ⟨P.at' 2012, 36⟩) (Offset.contains P.S (by omega) (by omega) (by omega))
      (fun r hr => sav_disj hp (hrs r hr)) (by decide)]
    exact he.savlr
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    rcases hrs r hr with h | h | h
    · exact ⟨P.scrR, by simp, fun x hx => sub_scr0 (P := P) (n := 2012) (by omega) x (h x hx)⟩
    · exact ⟨P.aR, by simp, h⟩
    · exact ⟨below σ 8, by simp, h⟩

/-- `Env` after a call that keeps the callee-saved registers and writes where
code may write. -/
theorem Env.kept {s s' : State} (he : Env P σ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, P.Wr σ r) : Env P σ s' :=
  he.step hp hk.frame hrs (hk.cs .r5 (by decide) (by decide)) (hk.cs .r6 (by decide) (by decide)) hk.rd hk.wr hk.sp

omit hp in
/-- `Env` after a block that writes no memory and none of `r4`–`r11`. -/
theorem Env.regs {s s' : State} (he : Env P σ s) (hr : Regs s s') : Env P σ s' :=
  ⟨hr.rd.trans he.rd, hr.wr.trans he.wr, hr.sp.trans he.sp, (hr.cs .r5 (by decide) (by decide)).trans he.r5,
    (hr.cs .r6 (by decide) (by decide)).trans he.r6, by rw [hr.mem]; exact he.sav, by rw [hr.mem]; exact he.savlr,
    by rw [hr.mem]; exact he.frame⟩

/-- The message is not written. -/
theorem msg_frame {s : State} (he : Env P σ s) : bytesAt s.mem (State.addr P.sd) P.len = P.msg σ :=
  MlKem.bytesAt_frame he.frame (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.sd_a, hp.sd_scr, hp.b_sd.symm]) (by have := hp.len_lt; omega)

omit hp in
/-- A part of the working space below the saved registers. -/
theorem wr_scr {a n : Nat} (h : a + n ≤ 2012) : P.Wr σ ⟨P.at' a, n⟩ :=
  .inl (Offset.sub_base _ h)

omit hp in
theorem wr_scr0 {n : Nat} (h : n ≤ 2012) : P.Wr σ ⟨P.S, n⟩ := .inl (Region.sub_prefix h)

omit hp in
theorem wr_below {s : State} (h : s.sp = σ.sp) : P.Wr σ (below s 8) := .inr (.inr (by rw [below_eq h]; exact fun _ h => h))

end

/-! ## The sponge -/

/-- The registers of the sponge's arguments: the parameter in `r7`, the
message in `r8` and its length in `r9`. -/
structure J0 (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  r7 : s.gpr .r7 = P.prm
  r8 : s.gpr .r8 = P.sd
  r9 : s.gpr .r9 = BitVec.ofNat 32 P.len

/-- `J0` after a block that writes no memory and none of `r4`–`r11`. -/
theorem J0.regs {P : Sp} {σ s s' : State} (h : J0 P σ s) (hr : Regs s s') : J0 P σ s' :=
  ⟨h.env.regs hr, (hr.cs .r7 (by decide) (by decide)).trans h.r7, (hr.cs .r8 (by decide) (by decide)).trans h.r8,
    (hr.cs .r9 (by decide) (by decide)).trans h.r9⟩

theorem J0.kept {P : Sp} {σ s s' : State} (hp : SpOk P σ) (h : J0 P σ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, P.Wr σ r) : J0 P σ s' :=
  ⟨h.env.kept hp hk hrs, (hk.cs .r7 (by decide) (by decide)).trans h.r7,
    (hk.cs .r8 (by decide) (by decide)).trans h.r8, (hk.cs .r9 (by decide) (by decide)).trans h.r9⟩

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  j0 : J0 P σ s
  zero : stateAt s.mem P.S = Spec.Sha3.zero
  args : AbsorbArgs s P.scr (P.scr + BitVec.ofNat 32 200) P.sd rate 0 P.len

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem absArgs_of {rate : Nat} (hr : rate ∈ rates) {s : State} (he : Env P σ s) (g0 : s.gpr .r0 = P.scr)
    (g1 : s.gpr .r1 = BitVec.ofNat 32 rate) (g2 : s.gpr .r2 = BitVec.ofNat 32 0) (g3 : s.gpr .r3 = P.sd)
    (g12 : s.gpr .r12 = BitVec.ofNat 32 P.len) (glr : s.gpr .lr = P.scr + BitVec.ofNat 32 200) :
    AbsorbArgs s P.scr (P.scr + BitVec.ofNat 32 200) P.sd rate 0 P.len := by
  have fs := hp.fscr
  have eb := below_eq he.sp
  exact {
    r0 := g0, r1 := g1, r2 := g2, r3 := g3, r12 := g12, lr := glr
    hrate := hr, hpos := rate_pos hr, hlen := hp.len_lt, sp := by rw [he.sp]; exact hp.sp8
    fst := fit_le (by decide) fs, fdata := hp.fsd, fscr := fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_scr := by rw [regA_at hp (by decide)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    d_data_st := hp.sd_scr.sub_right (sub_scr0 (by decide))
    d_data_scr := by rw [regA_at hp (by decide)]; exact hp.sd_scr.sub_right (sub_scr (by decide))
    b_st := by rw [eb]; exact hp.b_scr.sub_right (sub_scr0 (by decide))
    b_scr := by rw [eb, regA_at hp (by decide)]; exact hp.b_scr.sub_right (sub_scr (by decide))
    b_data := by rw [eb]; exact hp.b_sd
    cw := by
      rw [regA_at hp (by decide)]
      refine covScr hp he fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]
    cr := fun x n ⟨r, hr, hc⟩ => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (by rw [he.rd]; exact hp.rd), hc⟩ }

end

theorem movs_ok {rate : Nat} (er : encodable (BitVec.ofNat 32 rate) = true) (s : State) :
    WP isa (.block [.mov .r0 (.reg .r6), .mov .r1 (.imm (BitVec.ofNat 32 rate)), .mov .r2 (.imm 0),
      .mov .r3 (.reg .r8), .mov .r12 (.reg .r9), .dp .add .lr .r6 (.imm 200)]) s fun s' =>
      Regs s s' ∧ s'.gpr .r0 = s.gpr .r6 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
        s'.gpr .r3 = s.gpr .r8 ∧ s'.gpr .r12 = s.gpr .r9 ∧ s'.gpr .lr = s.gpr .r6 + BitVec.ofNat 32 200 := by
  run_block [er, and_self, and_true]
  refine ⟨regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mov12_ok (s : State) :
    WP isa (.block [.mov .r12 (.imm 0)]) s fun s' => s'.gpr = (s.setReg .r12 0).gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

theorem ne_r12 {r : Reg} (hr : r ∈ preserved) : r ≠ .r12 := by
  rintro rfl; exact absurd hr (by decide)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk1_ok {rate : Nat} (hr : rate ∈ rates) (er : encodable (BitVec.ofNat 32 rate) = true) {s : State}
    (h : J0 P σ s) : WP isa (.block (absArgs rate)) s (J1 rate P σ) := by
  unfold absArgs zeroState
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mov12_ok s) fun s1 ⟨g1, m1, rd1, wr1, sp1⟩ => ?_
  rw [WP.block_append_iff]
  have k1 : ∀ r ∈ preserved, s1.gpr r = s.gpr r := fun r hr => by
    rw [g1, gpr_setReg_of_ne _ _ (ne_r12 hr)]
  have e6 : s1.gpr .r6 = P.scr := (k1 .r6 (by decide)).trans h.env.r6
  refine WP.mono (zeroWords_ok .r6 (s₁ := s1) (by rw [g1, gpr_setReg_self])
    (by rw [e6]; exact fit_le (by decide) hp.fscr)
    fun k hk => by rw [e6, wr1]; exact inScr hp h.env (by omega)) fun s2 h2 => ?_
  refine WP.mono (movs_ok er s2) fun s3 ⟨R3, g0, g1', g2, g3, g12, glr⟩ => ?_
  have k3 : ∀ r ∈ preserved, r ≠ .lr → s3.gpr r = s.gpr r := fun r hr hl => by
    rw [R3.cs r hr hl, h2.gpr, k1 r hr]
  have e2 : ∀ r ∈ preserved, s2.gpr r = s.gpr r := fun r hr => by rw [h2.gpr, k1 r hr]
  have fr : Frame [⟨P.S, 200⟩] s.mem s3.mem := by
    rw [R3.mem, ← m1]
    have := h2.frame
    rwa [e6] at this
  have he : Env P σ s3 := h.env.step hp fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact wr_scr0 (by decide))
    (k3 .r5 (by decide) (by decide)) (k3 .r6 (by decide) (by decide))
    (by rw [R3.rd, h2.rd, rd1]) (by rw [R3.wr, h2.wr, wr1]) (by rw [R3.sp, h2.sp, sp1])
  have hz := h2.zero
  rw [e6] at hz
  refine ⟨⟨he, (k3 .r7 (by decide) (by decide)).trans h.r7, (k3 .r8 (by decide) (by decide)).trans h.r8,
    (k3 .r9 (by decide) (by decide)).trans h.r9⟩, by rw [R3.mem]; exact stateAt_zero hz,
    absArgs_of hp hr he (by rw [g0, e2 .r6 (by decide), h.env.r6]) g1' g2
      (by rw [g3, e2 .r8 (by decide), h.r8]) (by rw [g12, e2 .r9 (by decide), h.r9])
      (by rw [glr, e2 .r6 (by decide), h.env.r6])⟩

end


/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  j0 : J0 P σ s
  repr : Spec.Sha3.Repr s.mem P.S rate (P.msg σ)
  r0 : s.gpr .r0 = BitVec.ofNat 32 (P.len % rate)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

omit hp in
/-- What `absorb`, `pad` and `squeeze` write, where code may write. -/
theorem wr_calls {s : State} (he : Env P σ s) {rs : List Region}
    (h : ∀ r ∈ rs, (∃ a n, a + n ≤ 2012 ∧ r = ⟨P.at' a, n⟩) ∨ (∃ n, n ≤ 2012 ∧ r = ⟨P.S, n⟩) ∨ r = below s 8) :
    ∀ r ∈ rs, P.Wr σ r := fun r hr => by
  rcases h r hr with ⟨a, n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | rfl
  exacts [wr_scr hn, wr_scr0 hn, wr_below he.sp]

theorem call1_ok {rate : Nat} {s : State} (h : J1 rate P σ s) :
    WP isa absorbCall s (J2 rate P σ) := by
  refine absorb_ok h.args fun s' hk hr h0 => ⟨h.j0.kept hp hk (wr_calls h.j0.env fun r hr => ?_), ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl ⟨200, by decide, rfl⟩)
    · exact .inl ⟨200, 640, by decide, regA_at hp (by decide) _⟩
    · exact .inr (.inr rfl)
  · have := hr [] (MlKem.repr_nil h.zero) (by simp)
    rwa [List.nil_append, msg_frame hp h.j0.env] at this
  · apply BitVec.eq_of_toNat_eq
    have := Nat.mod_lt P.len (rate_pos h.args.hrate)
    have := rates_lt h.args.hrate
    rw [h0, Nat.zero_add, toNat_ofNat32 (by omega)]

end

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  j0 : J0 P σ s
  repr : Spec.Sha3.Repr s.mem P.S rate (P.msg σ)
  args : PadArgs s P.scr (P.scr + BitVec.ofNat 32 200) rate (P.len % rate) 0x1f

theorem pmovs_ok {rate : Nat} (er : encodable (BitVec.ofNat 32 rate) = true) (s : State) :
    WP isa (.block (padArgs rate)) s fun s' =>
      Regs s s' ∧ s'.gpr .r0 = s.gpr .r6 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧ s'.gpr .r2 = s.gpr .r0 ∧
        s'.gpr .r3 = 0x1f ∧ s'.gpr .lr = s.gpr .r6 + BitVec.ofNat 32 200 := by
  run_block [padArgs, er, and_self, and_true]
  refine ⟨regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk2_ok {rate : Nat} (hr : rate ∈ rates) (er : encodable (BitVec.ofNat 32 rate) = true) {s : State}
    (h : J2 rate P σ s) : WP isa (.block (padArgs rate)) s (J3 rate P σ) := by
  refine WP.mono (pmovs_ok er s) fun s' ⟨R, g0, g1, g2, g3, glr⟩ => ?_
  have he := h.j0.env.regs R
  have fs := hp.fscr
  have eb := below_eq he.sp
  refine ⟨h.j0.regs R, by rw [R.mem]; exact h.repr, {
    r0 := by rw [g0, h.j0.env.r6], r1 := g1, r2 := by rw [g2, h.r0], r3 := g3,
    lr := by rw [glr, h.j0.env.r6]
    hrate := hr, hpos := Nat.mod_lt _ (rate_pos hr), sp := by rw [he.sp]; exact hp.sp8
    fst := fit_le (by decide) fs, fscr := fit_add (fit_le (by decide) fs) (by decide) (by decide)
    d_st_scr := by rw [regA_at hp (by decide)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    b_st := by rw [eb]; exact hp.b_scr.sub_right (sub_scr0 (by decide))
    b_scr := by rw [eb, regA_at hp (by decide)]; exact hp.b_scr.sub_right (sub_scr (by decide))
    cw := by
      rw [regA_at hp (by decide)]
      refine covScr hp he fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩] }⟩

end

/-- After padding. -/
structure J4 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  j0 : J0 P σ s
  st : stateAt s.mem P.S = padded rate Spec.Sha3.shakeSuffix (P.msg σ)

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call2_ok {rate : Nat} {s : State} (h : J3 rate P σ s) : WP isa padCall s (J4 rate P σ) := by
  refine pad_ok h.args fun s' hk hst => ⟨h.j0.kept hp hk (wr_calls h.j0.env fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl ⟨200, by decide, rfl⟩)
    · exact .inl ⟨200, 640, by decide, regA_at hp (by decide) _⟩
    · exact .inr (.inr rfl)
  · rw [hst (P.msg σ) h.repr (by rw [MlKem.bytesAt_length]), MlKem.shakeSuffix32]

end

/-- The arguments of `squeeze`. -/
structure J5 (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  j4 : J4 rate P σ s
  args : SqueezeArgs s P.scr (P.scr + BitVec.ofNat 32 200) (P.scr + BitVec.ofNat 32 840) rate 0 outlen

theorem smovs_ok {rate outlen : Nat} (er : encodable (BitVec.ofNat 32 rate) = true)
    (eo : encodable (BitVec.ofNat 32 outlen) = true) (s : State) :
    WP isa (.block (sqzArgs rate outlen)) s fun s' =>
      Regs s s' ∧ s'.gpr .r0 = s.gpr .r6 ∧ s'.gpr .r1 = BitVec.ofNat 32 rate ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
        s'.gpr .r3 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s'.gpr .r12 = BitVec.ofNat 32 outlen ∧
        s'.gpr .lr = s.gpr .r6 + BitVec.ofNat 32 200 := by
  run_block [sqzArgs, er, eo, and_self, and_true]
  refine ⟨regs_cs _ ?_, by simp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2012)
    (er : encodable (BitVec.ofNat 32 rate) = true) (eo : encodable (BitVec.ofNat 32 outlen) = true) {s : State}
    (h : J4 rate P σ s) : WP isa (.block (sqzArgs rate outlen)) s (J5 rate outlen P σ) := by
  refine WP.mono (smovs_ok er eo s) fun s' ⟨R, g0, g1, g2, g3, g12, glr⟩ => ?_
  have he := h.j0.env.regs R
  have fs := hp.fscr
  have eb := below_eq he.sp
  refine ⟨⟨h.j0.regs R, by rw [R.mem]; exact h.st⟩, {
    r0 := by rw [g0, h.j0.env.r6], r1 := g1, r2 := g2, r3 := by rw [g3, h.j0.env.r6], r12 := g12,
    lr := by rw [glr, h.j0.env.r6]
    hrate := hr, hpos := Nat.zero_le _, hlen := by omega, sp := by rw [he.sp]; exact hp.sp8
    fst := fit_le (by decide) fs, fscr := fit_add (fit_le (by decide) fs) (by decide) (by decide)
    fout := by rw [BitVec.toNat_add, toNat_ofNat32 (by decide)]; omega
    d_st_out := by rw [regA_at hp (by decide)]; exact Offset.base_disjoint _ (by omega) (by omega)
    d_st_scr := by rw [regA_at hp (by decide)]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    d_out_scr := by
      rw [regA_at hp (by decide), regA_at hp (by decide)]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    b_st := by rw [eb]; exact hp.b_scr.sub_right (sub_scr0 (by decide))
    b_out := by rw [eb, regA_at hp (by decide)]; exact hp.b_scr.sub_right (sub_scr (by omega))
    b_scr := by rw [eb, regA_at hp (by decide)]; exact hp.b_scr.sub_right (sub_scr (by decide))
    cw := by
      rw [regA_at hp (by decide), regA_at hp (by decide)]
      refine covScr hp he fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩] }⟩

end

/-- After squeezing: the output, and the parameter in `r7`. -/
structure J6 (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  r7 : s.gpr .r7 = P.prm
  out : bytesAt s.mem (P.at' 840) outlen =
    squeezeFrom rate (padded rate Spec.Sha3.shakeSuffix (P.msg σ)) 0 outlen

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem call3_ok {rate outlen : Nat} (ho : 840 + outlen ≤ 2012) {s : State} (h : J5 rate outlen P σ s) :
    WP isa squeezeCall s (J6 rate outlen P σ) := by
  refine squeeze_ok h.args fun s' hk hout _ _ => ?_
  have j0 := h.j4.j0.kept hp hk (wr_calls h.j4.j0.env fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inr (.inl ⟨200, by decide, rfl⟩)
    · exact .inl ⟨840, outlen, by omega, regA_at hp (by decide) _⟩
    · exact .inl ⟨200, 640, by decide, regA_at hp (by decide) _⟩
    · exact .inr (.inr rfl))
  refine ⟨j0.env, j0.r7, ?_⟩
  rw [← at_eq hp (by decide), hout, show State.addr P.scr = P.S from rfl, h.j4.st]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE (of rate `rate`) of the
message at `scratch + 840`. -/
theorem sponge_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2012)
    (er : encodable (BitVec.ofNat 32 rate) = true) (eo : encodable (BitVec.ofNat 32 outlen) = true) {s : State}
    (h : J0 P σ s) : WP isa (sponge rate outlen) s (J6 rate outlen P σ) :=
  WP.seq (WP.mono (blk1_ok hp hr er h) fun _ h1 =>
    WP.seq (WP.mono (call1_ok hp h1) fun _ h2 => WP.seq (WP.mono (blk2_ok hp hr er h2) fun _ h3 =>
      WP.seq (WP.mono (call2_ok hp h3) fun _ h4 => WP.seq (WP.mono (blk3_ok hp hr ho er eo h4) fun _ h5 =>
        call3_ok hp ho h5)))))

end


/-! ## Constant time

Two runs, from entry states `σ₁` and `σ₂` whose calls agree (the same `P`,
and the same stack pointer), each related to its own entry state by the
invariants of the correctness proof. -/

/-- Code the taint analysis proves constant time from the registers `rs`,
which hold the same values in runs related by `R`. -/
theorem taintRel {R : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, R x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa R c fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hr a b hab)) h

/-- A piece that leaks the same in both runs, with what correctness says of
each. -/
theorem relW {c : Prog isa} {R : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa R c fun _ _ => True) (hw : ∀ a b, R a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa R c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- `rs` hold the same values in both runs. -/
theorem env_regs {P : Sp} {σ₁ σ₂ a b : State} (e₁ : Env P σ₁ a) (e₂ : Env P σ₂ b) :
    a.gpr .r5 = b.gpr .r5 ∧ a.gpr .r6 = b.gpr .r6 := ⟨by rw [e₁.r5, e₂.r5], by rw [e₁.r6, e₂.r6]⟩

theorem j0_regs {P : Sp} {σ₁ σ₂ a b : State} (h₁ : J0 P σ₁ a) (h₂ : J0 P σ₂ b) :
    ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [(env_regs h₁.env h₂.env).1, (env_regs h₁.env h₂.env).2, by rw [h₁.r7, h₂.r7],
    by rw [h₁.r8, h₂.r8], by rw [h₁.r9, h₂.r9]]


section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) (hsp : σ₁.sp = σ₂.sp)
include hp₁ hp₂ hsp

/-- The sponge leaks the same in both runs. The blocks are proven constant
time by the taint analysis (`c1`, `c2`, `c3`: `by taint_decide` for the
rate and length used). -/
theorem sponge_ct {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2012)
    (er : encodable (BitVec.ofNat 32 rate) = true) (eo : encodable (BitVec.ofNat 32 outlen) = true)
    {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
    (c1 : (VG.Arm.taint.check (Taint.ofRegs [.r5, .r6, .r7, .r8, .r9]) (.block (absArgs rate)) h1).isSome = true)
    (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r0, .r5, .r6]) (.block (padArgs rate)) h2).isSome = true)
    (c3 : (VG.Arm.taint.check (Taint.ofRegs [.r5, .r6]) (.block (sqzArgs rate outlen)) h3).isSome = true) :
    RelCT isa (fun a b => J0 P σ₁ a ∧ J0 P σ₂ b) (sponge rate outlen)
      (fun a b => J6 rate outlen P σ₁ a ∧ J6 rate outlen P σ₂ b) := by
  refine RelCT.seq (relW (taintRel _ (fun a b h => j0_regs h.1 h.2) c1)
    fun a b h => ⟨blk1_ok hp₁ hr er h.1, blk1_ok hp₂ hr er h.2⟩) ?_
  refine RelCT.seq (relW (absorb_ct fun a b h => ⟨by rw [h.1.j0.env.sp, h.2.j0.env.sp, hsp], _, _, _, _, _, _,
      h.1.args, h.2.args⟩) fun a b h => ⟨call1_ok hp₁ h.1, call1_ok hp₂ h.2⟩) ?_
  refine RelCT.seq (relW (taintRel _ (fun a b h r hr' => ?_) c2)
    fun a b h => ⟨blk2_ok hp₁ hr er h.1, blk2_ok hp₂ hr er h.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    exacts [by rw [h.1.r0, h.2.r0], (env_regs h.1.j0.env h.2.j0.env).1, (env_regs h.1.j0.env h.2.j0.env).2]
  refine RelCT.seq (relW (pad_ct fun a b h => ⟨by rw [h.1.j0.env.sp, h.2.j0.env.sp, hsp], _, _, _, _, _,
      h.1.args, h.2.args⟩) fun a b h => ⟨call2_ok hp₁ h.1, call2_ok hp₂ h.2⟩) ?_
  refine RelCT.seq (relW (taintRel _ (fun a b h r hr' => ?_) c3)
    fun a b h => ⟨blk3_ok hp₁ hr ho er eo h.1, blk3_ok hp₂ hr ho er eo h.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    exacts [(env_regs h.1.j0.env h.2.j0.env).1, (env_regs h.1.j0.env h.2.j0.env).2]
  exact relW (squeeze_ct fun a b h => ⟨by rw [h.1.j4.j0.env.sp, h.2.j4.j0.env.sp, hsp], _, _, _, _, _, _,
      h.1.args, h.2.args⟩) fun a b h => ⟨call3_ok hp₁ ho h.1, call3_ok hp₂ ho h.2⟩

end

end VG.Proof.MlDsa.Arm.Sample
