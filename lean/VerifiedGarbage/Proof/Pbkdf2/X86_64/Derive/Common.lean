import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Proof.Framework.X86_64.RegBlock
import VerifiedGarbage.Impl.Pbkdf2.X86_64.Derive

/-!
# PBKDF2-HMAC-SHA-256 on x86-64: the entry state, regions and invariant

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Pbkdf2.X86_64.Derive

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Proof.Sha256.X86_64 (contains_offset sub_offset toNat_ofNat_lt)

/-! ## Arithmetic -/

theorem se_ofNat {k : Nat} (h : k < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem add_ofNat (a : Addr) (o j : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The entry state -/

section
variable (s₀ : State)

abbrev pw : Addr := s₀.gpr .rdi
abbrev pl : Nat := (s₀.gpr .rsi).toNat
abbrev sa : Addr := s₀.gpr .rdx
abbrev sl : Nat := (s₀.gpr .rcx).toNat
/-- The iteration count. -/
abbrev cc : Nat := ((s₀.gpr .r8).setWidth 32).toNat
abbrev op : Addr := s₀.gpr .r9
abbrev ol : Nat := (stackArg s₀ 0).toNat
abbrev sc : Addr := stackArg s₀ 1

abbrev pwR : Region := ⟨pw s₀, pl s₀⟩
abbrev saR : Region := ⟨sa s₀, sl s₀⟩
abbrev outR : Region := ⟨op s₀, ol s₀⟩
abbrev scR : Region := ⟨sc s₀, 2048⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The stack below the return address that the calls use. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 24
/-- `scratch[o, o + n)`. -/
abbrev sR (o n : Nat) : Region := ⟨sc s₀ + BitVec.ofNat 64 o, n⟩

/-- The password and the salt. -/
abbrev P : List Byte := bytesAt s₀.mem (pw s₀) (pl s₀)
abbrev S : List Byte := bytesAt s₀.mem (sa s₀) (sl s₀)
/-- The HMAC key `K₀`. -/
abbrev k0 : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 (P s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scR s₀]
  p_o : (pwR s₀).Disjoint (outR s₀)
  p_s : (pwR s₀).Disjoint (scR s₀)
  a_o : (saR s₀).Disjoint (outR s₀)
  a_s : (saR s₀).Disjoint (scR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  o_g : (outR s₀).Disjoint (argR s₀)
  s_g : (scR s₀).Disjoint (argR s₀)
  ret_p : (retR s₀).Disjoint (pwR s₀)
  ret_a : (retR s₀).Disjoint (saR s₀)
  ret_o : (retR s₀).Disjoint (outR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  ret_g : (retR s₀).Disjoint (argR s₀)
  stk_p : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (pwR s₀)
  stk_a : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (saR s₀)
  stk_o : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (outR s₀)
  stk_s : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (scR s₀)
  stk_g : (⟨s₀.gpr .rsp - 24, 24⟩ : Region).Disjoint (argR s₀)
  nw_p : (pw s₀).toNat + pl s₀ ≤ 2 ^ 64
  nw_a : (sa s₀).toNat + sl s₀ ≤ 2 ^ 64
  nw_o : (op s₀).toNat + ol s₀ ≤ 2 ^ 64
  nw_s : (sc s₀).toNat + 2048 ≤ 2 ^ 64
  pos : 0 < cc s₀
  len : ol s₀ ≤ (2 ^ 32 - 1) * 32

theorem pre_of {s₀ : State} (h : Proof.Pbkdf2.pbkdf2Sha256X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25⟩

theorem stkR_eq (s₀ : State) : stkR s₀ = ⟨s₀.gpr .rsp - 24, 24⟩ := rfl

/-! ## Regions -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Pre.stk_p' : (stkR s₀).Disjoint (pwR s₀) := hp.stk_p
theorem Pre.stk_a' : (stkR s₀).Disjoint (saR s₀) := hp.stk_a
theorem Pre.stk_o' : (stkR s₀).Disjoint (outR s₀) := hp.stk_o
theorem Pre.stk_s' : (stkR s₀).Disjoint (scR s₀) := hp.stk_s
theorem Pre.stk_g' : (stkR s₀).Disjoint (argR s₀) := hp.stk_g

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

/-- The part of the stack a call from `rsp` uses, with its callee's calls. -/
theorem below_stk (s₀ : State) {n : Nat} (h : n ≤ 24) : Region.Sub (below (s₀.gpr .rsp) n) (stkR s₀) :=
  below_sub h (by omega)

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

/-! ## Covering the callees' regions -/

/-- A part of the scratch space, as `Covers.of_sub` needs it. -/
theorem cov_sR {s₀ : State} {rs : List Region} (hin : scR s₀ ∈ rs) {o n : Nat}
    (h : o + n ≤ 2048) :
    ∃ r' ∈ rs, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR s₀, hin, o, rfl, h⟩

/-- A region itself, as `Covers.of_sub` needs it. -/
theorem cov_self {rs : List Region} {r : Region} (hin : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, hin, 0, by simp, by simp⟩

/-! ## Memory -/

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Iterate.frame_bytesAt hf hd hn

/-- A streaming state outside a frame is unchanged. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 96⟩ r) {msg : List Byte} (h : Repr m p msg) : Repr m' p msg :=
  Proof.Sha256.Stream.repr_congr (fun i hi => hf.bytes (R := ⟨p, 96⟩) hd (by simp) hi) h

/-- A streaming state is its 96 bytes. -/
theorem repr_of_bytes {m m' : Mem} {p q : Addr} (h : bytesAt m' q 96 = bytesAt m p 96) {msg : List Byte}
    (hr : Repr m p msg) : Repr m' q msg := by
  have e : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := fun i hi => by
    rw [← Proof.Hmac.X86_64.bytesAt_getD' m' q hi, ← Proof.Hmac.X86_64.bytesAt_getD' m p hi, h]
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    exact Proof.Hmac.X86_64.stateAt_eq_of_bytes fun i hi => e i (by omega)
  · rw [← hr.2]
    have hl : msg.length % 64 < 64 := Nat.mod_lt _ (by omega)
    apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [show q + 32 + BitVec.ofNat 64 i = q + BitVec.ofNat 64 (32 + i) by
        simp only [BitVec.ofNat_add, BitVec.add_assoc]; rfl,
      show p + 32 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (32 + i) by
        simp only [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    exact e _ (by omega)

/-! ## Our caller's registers and `c` -/

/-- Our caller's `rbx, rbp, r12–r15`, and `c`, saved in `scratch[424, 476)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ p ∈ dSaved, m.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1) ∧
  m.readW (sc s₀ + BitVec.ofNat 64 472) 32 = (s₀.gpr .r8).setWidth 32

theorem dSaved_off : ∀ p ∈ dSaved, 424 ≤ p.2 ∧ p.2 + 8 ≤ 472 := by decide

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sR s₀ 424 52).Disjoint r) : Saved s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have := dSaved_off p hp
    rw [hf.readW (contains_sR s₀ (o := 424) (n := 52) (w := 64 / 8) this.1 (by omega) (by omega)) hd
      (by decide)]
    exact h.1 p hp
  · rw [hf.readW (contains_sR s₀ (o := 424) (n := 52) (w := 32 / 8) (a := 472) (by omega) (by omega)
      (by omega)) hd (by decide)]
    exact h.2

/-! ## Where the code writes -/

/-- `out`, the scratch space but the saved registers and `c`, and the stack below the return
address. -/
abbrev wk (s₀ : State) : List Region := [outR s₀, sR s₀ 0 424, sR s₀ 476 1572, stkR s₀]

theorem wk_out (s₀ : State) : ∃ r' ∈ wk s₀, Region.Sub (outR s₀) r' := ⟨outR s₀, by simp, fun _ h => h⟩

theorem wk_lo (s₀ : State) {o n : Nat} (h : o + n ≤ 424) : ∃ r' ∈ wk s₀, Region.Sub (sR s₀ o n) r' :=
  ⟨sR s₀ 0 424, by simp, sR_sub_sR s₀ (by omega) (by omega) (by omega)⟩

theorem wk_hi (s₀ : State) {o n : Nat} (h₁ : 476 ≤ o) (h₂ : o + n ≤ 2048) :
    ∃ r' ∈ wk s₀, Region.Sub (sR s₀ o n) r' :=
  ⟨sR s₀ 476 1572, by simp, sR_sub_sR s₀ h₁ (by omega) (by omega)⟩

theorem wk_stk (s₀ : State) {sp : Addr} (hsp : sp = s₀.gpr .rsp) {n : Nat} (h : n ≤ 24) :
    ∃ r' ∈ wk s₀, Region.Sub (below sp n) r' := ⟨stkR s₀, by simp, by rw [hsp]; exact below_stk s₀ h⟩

theorem Pre.wk_saved {s₀ : State} (hp : Pre s₀) : ∀ r ∈ wk s₀, (sR s₀ 424 52).Disjoint r := by
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
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = sc s₀
  saved : Saved s₀ s.mem
  frame : Frame [outR s₀, scR s₀, stkR s₀] s₀.mem s.mem

theorem Base.step {s₀ s s' : State} (hp : Pre s₀) (h : Base s₀ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (rsp : s'.gpr .rsp = s.gpr .rsp) (rbx : s'.gpr .rbx = s.gpr .rbx) (hf : Frame (wk s₀) s.mem s'.mem) :
    Base s₀ s' :=
  ⟨rd.trans h.rd, wr.trans h.wr, rsp.trans h.rsp, rbx.trans h.rbx, h.saved.frame hf hp.wk_saved,
    h.frame.trans (wk_global hf)⟩

theorem Base.call {s₀ s s' : State} (hp : Pre s₀) (h : Base s₀ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hf : Frame (wk s₀) s.mem s'.mem) : Base s₀ s' :=
  h.step hp rd wr (cs _ (by simp [calleeSaved])) (cs _ (by simp [calleeSaved])) hf

/-- `Base` survives code that writes no memory and neither `rsp` nor `rbx`. -/
theorem Base.regs {s₀ s s' : State} (h : Base s₀ s) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (rsp : s'.gpr .rsp = s.gpr .rsp) (rbx : s'.gpr .rbx = s.gpr .rbx) (hm : s'.mem = s.mem) : Base s₀ s' :=
  ⟨rd.trans h.rd, wr.trans h.wr, rsp.trans h.rsp, rbx.trans h.rbx, hm ▸ h.saved, hm ▸ h.frame⟩

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

theorem Base.arg_eq : s.mem.readW (stackArgAddr s₀ 0) 64 = stackArg s₀ 0 := by
  have c : (argR s₀).Contains (stackArgAddr s₀ 0) (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine h.frame.readW c ?_ (by decide)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨hp.o_g.symm, hp.s_g.symm, hp.stk_g'.symm⟩

theorem Base.ret_eq : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
  refine h.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine ⟨hp.ret_o, hp.ret_s, ?_⟩
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

end

end VG.Proof.Pbkdf2.X86_64.Derive
