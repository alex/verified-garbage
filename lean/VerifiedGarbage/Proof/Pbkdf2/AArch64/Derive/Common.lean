import VerifiedGarbage.Proof.Pbkdf2.AArch64.Contract
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegBlock
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Impl.Pbkdf2.AArch64.Derive

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: the entry state, regions and invariant

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Pbkdf2.X86_64.Derive`), whose lemmas about memory
and the specification (which do not depend on the target) it uses. `s₀` is
the entry state; the body of the frame saving `x30` (`deriveMain`) runs from
`ini s₀`, with the stack pointer 16 bytes lower.
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64 VG.Impl.Pbkdf2.AArch64
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Proof.Sha256.AArch64 (contains_offset sub_offset toNat_ofNat_lt)

theorem add_ofNat (a : Addr) (o j : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The entry state -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .x0
abbrev pl : Nat := (s₀.gpr .x1).toNat
abbrev sa : Addr := s₀.gpr .x2
abbrev sl : Nat := (s₀.gpr .x3).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .x4).setWidth 32).toNat
abbrev op : Addr := s₀.gpr .x5
abbrev ol : Nat := (s₀.gpr .x6).toNat
abbrev sc : Addr := s₀.gpr .x7

abbrev pwR : Region := ⟨pw s₀, pl s₀⟩
abbrev saR : Region := ⟨sa s₀, sl s₀⟩
abbrev outR : Region := ⟨op s₀, ol s₀⟩
abbrev scR : Region := ⟨sc s₀, 2048⟩
/-- The stack our frame and the calls use. -/
abbrev stkR : Region := below s₀.sp 48
/-- `scratch[o, o + n)`. -/
abbrev sR (o n : Nat) : Region := ⟨sc s₀ + BitVec.ofNat 64 o, n⟩

/-- The password and the salt. -/
abbrev P : List Byte := bytesAt s₀.mem (pw s₀) (pl s₀)
abbrev S : List Byte := bytesAt s₀.mem (sa s₀) (sl s₀)
/-- The HMAC key `K₀`. -/
abbrev k0 : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 (P s₀)

/-- `c`, zero-extended. -/
abbrev c64 : BitVec 64 := ((s₀.gpr .x4).setWidth 32).setWidth 64

/-- The state the body of our frame starts in. -/
abbrev ini : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saR s₀]
  wr : s₀.wr = [outR s₀, scR s₀]
  p_o : (pwR s₀).Disjoint (outR s₀)
  p_s : (pwR s₀).Disjoint (scR s₀)
  a_o : (saR s₀).Disjoint (outR s₀)
  a_s : (saR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  sp48 : 48 ≤ s₀.sp.toNat
  stk_p : (⟨s₀.sp - 48, 48⟩ : Region).Disjoint (pwR s₀)
  stk_a : (⟨s₀.sp - 48, 48⟩ : Region).Disjoint (saR s₀)
  stk_o : (⟨s₀.sp - 48, 48⟩ : Region).Disjoint (outR s₀)
  stk_s : (⟨s₀.sp - 48, 48⟩ : Region).Disjoint (scR s₀)
  nw_p : (pw s₀).toNat + pl s₀ ≤ 2 ^ 64
  nw_a : (sa s₀).toNat + sl s₀ ≤ 2 ^ 64
  nw_o : (op s₀).toNat + ol s₀ ≤ 2 ^ 64
  nw_s : (sc s₀).toNat + 2048 ≤ 2 ^ 64
  pos : 0 < cc s₀
  len : ol s₀ ≤ (2 ^ 32 - 1) * 32

theorem pre_of {s₀ : State} (h : Proof.Pbkdf2.pbkdf2Sha256AArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

/-! ## Regions -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Pre.stk_p' : (stkR s₀).Disjoint (pwR s₀) := hp.stk_p
theorem Pre.stk_a' : (stkR s₀).Disjoint (saR s₀) := hp.stk_a
theorem Pre.stk_o' : (stkR s₀).Disjoint (outR s₀) := hp.stk_o
theorem Pre.stk_s' : (stkR s₀).Disjoint (scR s₀) := hp.stk_s

end

theorem sR_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 2048) : Region.Sub (sR s₀ o n) (scR s₀) :=
  sub_offset h (by omega)

/-- A part of a part of the scratch space. -/
theorem sR_sub_sR (s₀ : State) {a n b m : Nat} (h₁ : b ≤ a) (h₂ : a + n ≤ b + m) (h₃ : b + m ≤ 2048) :
    Region.Sub (sR s₀ a n) (sR s₀ b m) := by
  intro x hx
  simp only [Region.Contains] at *
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

/-- Two parts of the scratch space that do not overlap. -/
theorem sR_disj (s₀ : State) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 2048)
    (hb : b + n ≤ 2048) : (sR s₀ a m).Disjoint (sR s₀ b n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

theorem Pre.stk_sR {s₀ : State} (hp : Pre s₀) {o n : Nat} (h : o + n ≤ 2048) : (stkR s₀).Disjoint (sR s₀ o n) :=
  hp.stk_s'.sub_right (sR_sub s₀ h)

theorem Pre.sR_stk {s₀ : State} (hp : Pre s₀) {o n : Nat} (h : o + n ≤ 2048) : (sR s₀ o n).Disjoint (stkR s₀) :=
  (hp.stk_sR h).symm

theorem Pre.p_sR {s₀ : State} (hp : Pre s₀) {o n : Nat} (h : o + n ≤ 2048) : (pwR s₀).Disjoint (sR s₀ o n) :=
  hp.p_s.sub_right (sR_sub s₀ h)

theorem Pre.a_sR {s₀ : State} (hp : Pre s₀) {o n : Nat} (h : o + n ≤ 2048) : (saR s₀).Disjoint (sR s₀ o n) :=
  hp.a_s.sub_right (sR_sub s₀ h)

theorem Pre.o_sR {s₀ : State} (hp : Pre s₀) {o n : Nat} (h : o + n ≤ 2048) : (outR s₀).Disjoint (sR s₀ o n) :=
  hp.o_s.sub_right (sR_sub s₀ h)

theorem contains_sR (s₀ : State) {o n a w : Nat} (h₁ : o ≤ a) (h₂ : a + w ≤ o + n) (h₃ : o + n ≤ 2048) :
    (sR s₀ o n).Contains (sc s₀ + BitVec.ofNat 64 a) w := by
  simp only [Region.Contains]
  rw [show sc s₀ + BitVec.ofNat 64 a - (sc s₀ + BitVec.ofNat 64 o) = BitVec.ofNat 64 (a - o) by
    rw [show a = o + (a - o) by omega, BitVec.ofNat_add]; bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem Pre.in_sc {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) {a w : Nat} (h : a + w ≤ 2048) :
    InRegions s.wr (sc s₀ + BitVec.ofNat 64 a) w :=
  ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩

theorem Pre.in_sc' {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr) {a w : Nat} (h : a + w ≤ 2048) :
    InRegions (s.rd ++ s.wr) (sc s₀ + BitVec.ofNat 64 a) w :=
  let ⟨r, hr, hc⟩ := hp.in_sc hwr h; ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## The stack -/

/-- The frames of a callee called from the body of ours are in the stack. -/
theorem frame48 {wr : List Region} {sp : Addr} {d : Nat} {m m' : Mem}
    (h : Frame (wr ++ [below (sp - 16) (16 * d)]) m m') (hd : d ≤ 2) : Frame (wr ++ [below sp 48]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun x hx =>
        below_sub (a := 16 * d + 16) (b := 48) (by omega) (by omega) x (below_body sp (16 * d) x hx)⟩

/-- The frame a callee pushes, from the body of ours. -/
theorem stk16_sub (sp : Addr) : Region.Sub ⟨sp - 16 - 16, 16⟩ (below sp 48) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

/-- The two frames `vg_hmac_sha256_finalize` and the `vg_sha256_finalize` it calls push. -/
theorem stk32_sub (sp : Addr) : Region.Sub ⟨sp - 16 - 32, 32⟩ (below sp 48) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

theorem Pre.sp16 {s₀ : State} (hp : Pre s₀) : 16 ≤ (s₀.sp - 16).toNat := by
  have := hp.sp48; bv_omega

theorem Pre.sp32 {s₀ : State} (hp : Pre s₀) : 32 ≤ (s₀.sp - 16).toNat := by
  have := hp.sp48; bv_omega

/-- Our frame. -/
theorem fr_sub (sp : Addr) : Region.Sub ⟨sp - 16, 16⟩ (below sp 48) := by
  intro x hx; simp only [Region.Contains] at *; bv_omega

/-! ## Covering the callees' regions -/

/-- A part of the scratch space, as `Covers.of_sub` needs it. -/
theorem cov_sR {s₀ : State} {rs : List Region} (hin : scR s₀ ∈ rs) {o n : Nat} (h : o + n ≤ 2048) :
    ∃ r' ∈ rs, ∃ off, sc s₀ + BitVec.ofNat 64 o = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨scR s₀, hin, o, rfl, h⟩

/-- A region itself, as `Covers.of_sub` needs it. -/
theorem cov_self {rs : List Region} {p : Addr} {n : Nat} (hin : (⟨p, n⟩ : Region) ∈ rs) :
    ∃ r' ∈ rs, ∃ off, p = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
  ⟨⟨p, n⟩, hin, 0, by simp, by simp⟩

/-! ## Memory -/

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Pbkdf2.X86_64.Derive.frame_bytesAt hf hd hn

theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) {msg : List Byte} (h : Repr m p msg) : Repr m' p msg :=
  Proof.Pbkdf2.X86_64.Derive.repr_frame hf hd h

/-! ## Our caller's registers -/

/-- Our caller's `x19`–`x26`, saved in `scratch[424, 488)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  ∀ p ∈ dSaved, m.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

theorem dSaved_off : ∀ p ∈ dSaved, 424 ≤ p.2 ∧ p.2 + 8 ≤ 488 := by decide

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sR s₀ 424 64).Disjoint r) : Saved s₀ m' := fun p hp => by
  have := dSaved_off p hp
  rw [hf.readW (contains_sR s₀ (o := 424) (n := 64) (w := 64 / 8) this.1 (by omega) (by omega)) hd
    (by decide)]
  exact h p hp

/-! ## Where the code writes -/

/-- `out`, the scratch space but the saved registers, and the stack. -/
abbrev wk (s₀ : State) : List Region := [outR s₀, sR s₀ 0 424, sR s₀ 488 1560, stkR s₀]

theorem wk_lo (s₀ : State) {o n : Nat} (h : o + n ≤ 424) : ∃ r' ∈ wk s₀, Region.Sub (sR s₀ o n) r' :=
  ⟨sR s₀ 0 424, by simp, sR_sub_sR s₀ (by omega) (by omega) (by omega)⟩

theorem wk_hi (s₀ : State) {o n : Nat} (h₁ : 488 ≤ o) (h₂ : o + n ≤ 2048) :
    ∃ r' ∈ wk s₀, Region.Sub (sR s₀ o n) r' :=
  ⟨sR s₀ 488 1560, by simp, sR_sub_sR s₀ h₁ (by omega) (by omega)⟩

theorem wk_stk (s₀ : State) : ∃ r' ∈ wk s₀, Region.Sub (stkR s₀) r' := ⟨stkR s₀, by simp, fun _ h => h⟩

theorem Pre.wk_saved {s₀ : State} (hp : Pre s₀) : ∀ r ∈ wk s₀, (sR s₀ 424 64).Disjoint r := by
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨(hp.o_sR (by omega)).symm, sR_disj s₀ (by omega) (by omega) (by omega),
    sR_disj s₀ (by omega) (by omega) (by omega), hp.sR_stk (by omega)⟩

theorem wk_global {s₀ : State} {m m' : Mem} (h : Frame (wk s₀) m m') : Frame [outR s₀, scR s₀, stkR s₀] m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, sR_sub s₀ (by omega)⟩
    · exact ⟨scR s₀, by simp, sR_sub s₀ (by omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-! ## What holds throughout -/

structure Base (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp - 16
  x19 : s.gpr .x19 = sc s₀
  x25 : s.gpr .x25 = s₀.gpr .x6
  x26 : s.gpr .x26 = c64 s₀
  saved : Saved s₀ s.mem
  frame : Frame [outR s₀, scR s₀, stkR s₀] s₀.mem s.mem

theorem Base.step {s₀ s s' : State} (hp : Pre s₀) (h : Base s₀ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (sp : s'.sp = s.sp) (x19 : s'.gpr .x19 = s.gpr .x19) (x25 : s'.gpr .x25 = s.gpr .x25)
    (x26 : s'.gpr .x26 = s.gpr .x26) (hf : Frame (wk s₀) s.mem s'.mem) : Base s₀ s' :=
  ⟨rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, x19.trans h.x19, x25.trans h.x25, x26.trans h.x26,
    h.saved.frame hf hp.wk_saved, h.frame.trans (wk_global hf)⟩

/-- `Base` after a call, which keeps the callee-saved registers but `x30`. -/
theorem Base.call {s₀ s s' : State} (hp : Pre s₀) (h : Base s₀ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (sp : s'.sp = s.sp) (cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r)
    (hf : Frame (wk s₀) s.mem s'.mem) : Base s₀ s' :=
  h.step hp rd wr sp (cs _ (by decide) (by decide)) (cs _ (by decide) (by decide))
    (cs _ (by decide) (by decide)) hf

/-- `Base` survives code that writes no memory and none of `x19`, `x25`, `x26`. -/
theorem Base.regs {s₀ s s' : State} (h : Base s₀ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (sp : s'.sp = s.sp) (x19 : s'.gpr .x19 = s.gpr .x19) (x25 : s'.gpr .x25 = s.gpr .x25)
    (x26 : s'.gpr .x26 = s.gpr .x26) (hm : s'.mem = s.mem) : Base s₀ s' :=
  ⟨rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, x19.trans h.x19, x25.trans h.x25, x26.trans h.x26,
    hm ▸ h.saved, hm ▸ h.frame⟩

section
variable {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s)
include hp h

theorem Base.pw_eq : bytesAt s.mem (pw s₀) (pl s₀) = P s₀ :=
  frame_bytesAt h.frame (by
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨hp.p_o, hp.p_s, hp.stk_p'.symm⟩) (by have := hp.nw_p; omega)

theorem Base.salt_eq : bytesAt s.mem (sa s₀) (sl s₀) = S s₀ :=
  frame_bytesAt h.frame (by
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨hp.a_o, hp.a_s, hp.stk_a'.symm⟩) (by have := hp.nw_a; omega)

end

end VG.Proof.Pbkdf2.AArch64Derive
