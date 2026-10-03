import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT
import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixLoops
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit

/-!
# scryptROMix on x86-64: the precondition and the calls

The regions the function works on, and `BlockMixSpec`: what a call of the
verified `vg_scrypt_blockmix` does, from its `Verified` proof by `WP.call`.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

namespace Stream
export VG.Proof.MdStream.X86_64 (Upd)
end Stream

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c` writes scryptBlockMix of the `128 r` bytes at `rdi` to
`rdx`, with the 128 bytes at `r8` as working space. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : Addr) (r : Nat), s.gpr .rdi = src → s.gpr .rsi = BitVec.ofNat 64 r →
    s.gpr .rdx = dst → s.gpr .rcx = BitVec.ofNat 64 r → s.gpr .r8 = scr → 0 < r →
    128 * r < 2 ^ 64 →
    Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩ → Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩ →
    Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨src, 128 * r⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨dst, 128 * r⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨scr, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 64 → dst.toNat + 128 * r ≤ 2 ^ 64 → scr.toNat + 128 ≤ 2 ^ 64 →
    InRegions (s.rd ++ s.wr) src (128 * r) → InRegions s.wr dst (128 * r) →
    InRegions s.wr scr 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr →
        (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨dst, 128 * r⟩, ⟨scr, 128⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
        bytesAt s'.mem dst (128 * r) = blockMix r (bytesAt s.mem src (128 * r)) → Q s') →
    WP isa (.call "vg_scrypt_blockmix" c) s Q

theorem blockMix_depth : Impl.Scrypt.X86_64.blockMix.depth = 1 := by decide +kernel

theorem blockMix_nosp : NoSp Impl.Scrypt.X86_64.blockMix := by
  have : ((instrs Impl.Scrypt.X86_64.blockMix).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The 8 bytes below the stack pointer after a call are within the 16 below it before. -/
theorem below8_sub (sp : Addr) : Region.Sub (below (sp - 8) 8) (below sp 16) :=
  below_callee sp 8

/-- The return address slot of a call from `sp`. -/
theorem ret8_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) := by
  intro a h
  simp only [Region.Contains] at h ⊢
  have e : a - (sp - BitVec.ofNat 64 16) = (a - (sp - 8)) + 8 := by bv_omega
  rw [e, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
  have := Nat.mod_le ((a - (sp - 8)).toNat + 8) (2 ^ 64)
  omega

/-- What a call of `vg_scrypt_blockmix` needs: its contract's precondition,
once the return address is stored and its permissions are narrowed. -/
theorem bm_pre {s : State} {src dst scr : Addr} {r : Nat} (hdi : s.gpr .rdi = src)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 r) (hdx : s.gpr .rdx = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 r)
    (hr8 : s.gpr .r8 = scr) (hr : 0 < r) (hlt : 128 * r < 2 ^ 64)
    (hds : Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩) (hsd : Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩)
    (bsrc : (below (s.gpr .rsp) 16).Disjoint ⟨src, 128 * r⟩)
    (bdst : (below (s.gpr .rsp) 16).Disjoint ⟨dst, 128 * r⟩)
    (bscr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 64) (ndst : dst.toNat + 128 * r ≤ 2 ^ 64)
    (nscr : scr.toNat + 128 ≤ 2 ^ 64)
    (isrc : InRegions (s.rd ++ s.wr) src (128 * r)) (idst : InRegions s.wr dst (128 * r))
    (iscr : InRegions s.wr scr 128) :
    Proof.Scrypt.blockMixX86_64.pre
      (s.callEntry.withRegions [⟨src, 128 * r⟩] [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) ∧
    Covers ([⟨src, 128 * r⟩] ++ [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨dst, 128 * r⟩, ⟨scr, 128⟩] s.wr := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have tr : (BitVec.ofNat 64 r).toNat = r := Memory.toNat_ofNat_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  have cw := Covers.pair (Covers.one idst) (Covers.one iscr)
  refine ⟨?_, ?_, cw⟩
  · simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx,
      hr8, tr, c128]
    refine ⟨trivial, trivial, hds, hsd, hss, ?_, ?_, ?_, ?_, ?_, nsrc, ndst, nscr, trivial, hr⟩
    · exact bdst.sub_left (ret8_sub _)
    · exact bscr.sub_left (ret8_sub _)
    · exact bsrc.sub_left (below8_sub _)
    · exact bdst.sub_left (below8_sub _)
    · exact bscr.sub_left (below8_sub _)
  · have h1 := Covers.one isrc
    intro a n h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h1 a n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.X86_64.blockMix := by
  intro s src dst scr r hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr Q hQ
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have tr : (BitVec.ofNat 64 r).toNat = r := Memory.toNat_ofNat_lt (by omega)
  obtain ⟨p, c₁, c₂⟩ := bm_pre hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr
  refine WP.call (k := Proof.Scrypt.blockMixX86_64) BlockMix.blockMix_correct blockMix_nosp
    (by rw [blockMix_depth]; decide) p c₁ c₂ ?_
  intro s₂ hrd hwr hcs hf _ ⟨s₃, hm₃, _, hpost⟩
  simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hdi, hsi, hdx, hm₃, tr] at hpost
  rw [blockMix_depth] at hf
  refine hQ s₂ hrd hwr hcs (by simpa using hf) ?_
  rw [hpost]
  congr 1
  exact Memory.bytesAt_congr fun i hi =>
    callEntry_byte s (R := ⟨src, 128 * r⟩) (bsrc.sub_left (below_sub (by omega) (by omega)))
      (by show 128 * r ≤ 2 ^ 64; omega) hi

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .rdi
abbrev rr : Nat := (s₀.gpr .rsi).toNat
abbrev vP : Addr := s₀.gpr .rdx
abbrev vl : Nat := (s₀.gpr .rcx).toNat
abbrev sc : Addr := s₀.gpr .r8
/-- `N`. -/
abbrev NN : Nat := vl s₀ / rr s₀
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev vR : Region := ⟨vP s₀, vl s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, (rr s₀ + 2) * 128⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)
/-- `V[i]`. -/
abbrev vAt (i : Nat) : Addr := vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := sc s₀ + BitVec.ofNat 64 192

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (sc s₀) s₀.gpr rmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, vR s₀, scR s₀]
  b_v : (bR s₀).Disjoint (vR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  v_s : (vR s₀).Disjoint (scR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_v : (retR s₀).Disjoint (vR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_v : (stkR s₀).Disjoint (vR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  v_nw : (vP s₀).toNat + vl s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + (rr s₀ + 2) * 128 ≤ 2 ^ 64
  pos : 0 < rr s₀
  vl_eq : vl s₀ = rr s₀ * NN s₀
  pow : (NN s₀).isPowerOfTwo
  r9 : (s₀.gpr .r9).toNat = rr s₀ + 2

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  simp only [h18] at h2 h4 h5 h8 h11 h14
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_, h17, h18⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h16)).symm

theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem NN_pos : 0 < NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * rr s₀ * NN s₀ < 2 ^ 64 := by
  have e : 128 * rr s₀ * NN s₀ = vl s₀ * 128 := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [e]
  by_contra hc
  refine hp.v_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (sc s₀ - vP s₀).isLt
  omega

theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  have := v_lt hp
  have := NN_pos hp
  have : 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- `V[i]` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < NN s₀) : Region.Sub ⟨vAt s₀ i, 128 * rr s₀⟩ (vR s₀) := by
  have := v_lt hp
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  show Region.Sub ⟨vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vP s₀, vl s₀ * 128⟩
  exact Memory.sub_off (by rw [e]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  have hle : ∀ j, j < NN s₀ → 128 * rr s₀ * j + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := fun j hj => by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have h1 := hle i hi
  have h2 := hle k hk
  have hpos := hp.pos
  refine Memory.disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left
    have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    exact this
  · right
    have : 128 * rr s₀ * k + 128 * rr s₀ ≤ 128 * rr s₀ * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    exact this

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨tP s₀, 128 * rr s₀⟩ (scR s₀) := by
  have := hp.s_nw
  exact Memory.sub_off (by omega) (by omega)

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨sc s₀, 128⟩ (scR s₀) := Region.sub_prefix (by omega)

theorem t_w : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨sc s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := Memory.disj_off (sc s₀) (o₁ := 192) (n₁ := 128 * rr s₀) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  Memory.sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: the caller's registers and `N` -/

/-- Bytes `[128, 184)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨sc s₀ + BitVec.ofNat 64 128, 56⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  Saved s₀ m ∧ m.readW (sc s₀ + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 (NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 184) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← Memory.add_ofNat]
  exact Memory.sub_off (by omega) (by omega)

theorem saved_offs {p : Reg × Nat} (hp : p ∈ rmSaved) : 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 :=
  (show ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 by decide) p hp

theorem Kept.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : Kept s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (keepR s₀).Disjoint r) : Kept s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have ho := saved_offs hp
    rw [← h.1 p hp]
    exact hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ ho.1 (by omega))) (by decide)
  · rw [← h.2]
    exact hf.readW (r := ⟨sc s₀ + BitVec.ofNat 64 176, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (word_sub s₀ (by omega) (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (keepR s₀) (scR s₀) := s_sub s₀ (by omega)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem keep_b : (keepR s₀).Disjoint (bR s₀) := hp.b_s.symm.sub_left (keep_sub s₀)
theorem keep_v : (keepR s₀).Disjoint (vR s₀) := hp.v_s.symm.sub_left (keep_sub s₀)
theorem keep_stk : (keepR s₀).Disjoint (stkR s₀) := hp.stk_s.symm.sub_left (keep_sub s₀)

omit hp in
theorem keep_w : (keepR s₀).Disjoint ⟨sc s₀, 128⟩ := by
  have := Memory.disj_off (sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

theorem keep_t : (keepR s₀).Disjoint ⟨tP s₀, 128 * rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact Memory.disj_off (sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 192) (n₂ := 128 * rr s₀) (by omega)
    (by omega) (by omega) (by omega) (by omega)

omit hp in
theorem b_sub' : Region.Sub ⟨bP s₀, 128 * rr s₀⟩ (bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Stream.Upd s s' d (s.gpr d >>> n) → s'.zf = some ((s.gpr d >>> n) == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine Proof.MdStream.X86_64.WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_ rfl)
  · simp [exec, execShift, h₁, h₂]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl,
      rfl⟩

theorem wp_and {d r : Reg}
    (k : ∀ s', Stream.Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.MdStream.X86_64.WP.cons rfl (k _ (VG.Proof.MdStream.X86_64.Upd.flags _ _ _ _ _ _))

end

theorem shr_ofNat {a : Nat} (n : Nat) (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Memory.toNat_ofNat_lt h, Memory.toNat_ofNat_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: correctness

The prologue saves our caller's registers in `scratch` and computes `N`; step
2 and step 3 are loops whose bodies call `vg_scrypt_blockmix` (through
`BlockMixSpec`); the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_mov32i)
open VG.Proof.Sha256.Stream (writeBytes)

theorem frame_bytesAt' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Memory.frame_bytesAt hf hd hn

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sc s₀) s₀.gpr rmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame _ _ _ _ fun _ hp => in_s s₀ (by have := saved_offs hp; omega)

theorem prologue_eq : rmPrologue =
    ([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp, .store (at_ .r8 144) .r12,
     .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15, .store (at_ .r8 168) .r13] : List Instr) ++
    ([.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8), .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp,
      .store (at_ .r8 144) .r12, .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15,
      .store (at_ .r8 168) .r13] : List Instr) ++ rest)) s₀ Q := by
  refine Spill.save_then .r8 rmSaved (fun p hp' => ?_) (k _ rfl rfl rfl rfl)
  have := saved_offs hp'
  rw [hp.wr]; exact Memory.InRegions.of_mem (by simp) (in_s s₀ (by omega))

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  rax : s.gpr .rax = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = 1
  rcx : s.gpr .rcx = BitVec.ofNat 64 (2 * vl s₀)

set_option linter.unusedSimpArgs false in
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8),
     .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)]) s₁ (P1 s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_add fun e7 u7 => wp_mov fun f uf _ _ =>
    wp_mov32i fun h uh _ _ => wp_add fun i ui => WP.block_nil ?_
  have x0 : d.gpr .r14 = BitVec.ofNat 64 (rr s₀) := by
    rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (BlockMix.dbl x0)
  have x2 := u2.gpr.trans (BlockMix.dbl x1)
  have x3 := u3.gpr.trans (BlockMix.dbl x2)
  have x4 := u4.gpr.trans (BlockMix.dbl x3)
  have x5 := u5.gpr.trans (BlockMix.dbl x4)
  have x6 := u6.gpr.trans (BlockMix.dbl x5)
  have x7 : e7.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [u7.gpr.trans (BlockMix.dbl x6)]; exact congrArg (BitVec.ofNat _) (by omega)
  have xc : h.gpr .rcx = BitVec.ofNat 64 (vl s₀) := by
    simp (disch := decide) only [uh.other, uf.other, u7.other, u6.other, u5.other, u4.other,
      u3.other, u2.other, u1.other, ud.other, uc.other, ub.other, ua.other, g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ui.rd, uh.rd, uf.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, uf.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.mem, uh.mem, uf.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  all_goals simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other,
    ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, u7.other, x7,
    uf.gpr, uf.other, uh.gpr, uh.other, ui.gpr, ui.other, g, xc, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  all_goals first | rfl | decide |
    exact BlockMix.dbl (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block rmPrologue) s₀ (P1 s₀) := by
  rw [prologue_eq]
  exact save_ok hp fun _ g hrd hwr hm => setup_ok hp g hrd hwr hm

/-! ## Computing `N` -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = vAt s₀ i
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  x : bytesAt s.mem (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀)
  done : ∀ k < i, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)

theorem setupMem_kept (s₀ : State) :
    Kept s₀ ((saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (NN s₀))) :=
  ⟨Spill.Saved.writeW (saveMem_saved s₀) _ (fun _ hp => by have := saved_offs hp; omega)
    (fun _ hp => by have := saved_offs hp; omega) (by decide), Mem.readW_writeW_self64 _ _ _⟩

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (2 * NN s₀)

theorem nloop_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) : WP isa nLoop s (N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := v_lt hp
  have pos := hp.pos
  have e2 : rr s₀ * 2 ^ (e + 1) = 2 * vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_comm]
  have hNe : 2 * vl s₀ < 2 ^ 64 := by
    have : 128 * rr s₀ * NN s₀ = 128 * vl s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  refine WP.mono (nLoop_ok (r := rr s₀) (e := e) hp.pos (by omega) h.rax h.rdx
    (by rw [h.rcx, e2])) fun t ⟨rd, wr, mem, oth, rdx⟩ => ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r := oth
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem, h.mem],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx],
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [rdx, he, Nat.pow_succ, Nat.mul_comm]⟩

theorem setup2_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : N1 s₀ s) :
    WP isa (.block rmSetup) s (Inv2 s₀ 0) := by
  have lt := v_lt hp
  have n1 := NN_pos hp
  have : 2 * NN s₀ < 2 ^ 64 := by
    have : 2 * NN s₀ ≤ 128 * rr s₀ * NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine wp_shr (by decide) (by decide) fun t1 u1 _ => ?_
  have hd : t1.gpr .rdx = BitVec.ofNat 64 (NN s₀) := by
    rw [u1.gpr, h.rdx, shr_ofNat _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_store (a := sc s₀ + BitVec.ofNat 64 176)
    (by rw [BlockMix.ea_at, u1.other _ (by decide), h.r13])
    (by rw [u1.wr, h.wr, hp.wr]; exact Memory.InRegions.of_mem (by simp) (in_s s₀ (by omega)))
    fun t2 g2 m2 rd2 wr2 => wp_mov fun t3 u3 _ _ => wp_mov fun t4 u4 _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdx → r ≠ .r15 → r ≠ .rbp → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, g2, u1.other _ b]
  have hm : t4.mem = (saveMem s₀).writeW (sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (NN s₀)) := by
    rw [u4.mem, u3.mem, m2, hd, u1.mem, h.mem]
  have fr : Frame [scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, rd2, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, wr2, u1.wr, h.wr], by rw [g _ (by decide) (by decide) (by decide), h.rsp],
    by rw [g _ (by decide) (by decide) (by decide), h.rbx], ?_,
    by rw [g _ (by decide) (by decide) (by decide), h.r12],
    by rw [g _ (by decide) (by decide) (by decide), h.r13],
    by rw [g _ (by decide) (by decide) (by decide), h.r14], ?_,
    fr.mono (by simp), by rw [hm]; exact setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega)⟩
  · rw [u4.gpr, u3.other _ (by decide), g2, u1.other _ (by decide), h.r12]
    simp
  · rw [u4.other _ (by decide), u3.gpr, g2, hd]; rfl
  · refine frame_bytesAt' fr (fun r hr => ?_) (by have := r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub' (s₀ := s₀))

theorem start_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : P1 s₀ s) {rest : Prog isa}
    {Q : State → Prop} (hk : ∀ s', Inv2 s₀ 0 s' → WP isa rest s' Q) :
    WP isa (.seq nLoop (.seq (.block rmSetup) rest)) s Q :=
  WP.seq (WP.mono (nloop_ok hp h) fun _ h' => WP.seq (WP.mono (setup2_ok hp h') hk))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `rdi` is set. -/
abbrev bmTail : List Instr :=
  [.mov .rsi (.reg .r14), .shift .shr .rsi 7, .mov .rcx (.reg .rsi), .mov .rdx (.reg .rbx),
    .mov .r8 (.reg .r13)]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (bP s₀) (128 * rr s₀) := by
  rw [hp.wr]
  refine Memory.InRegions.of_mem (R := bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (sc s₀) 128 := by
  rw [hp.wr]
  refine Memory.InRegions.of_mem (R := scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem calleeSaved_tail {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Setting up and making the call, from `rdi = A`. -/
theorem bm_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State} {A : Addr}
    (hA : s.gpr .rdi = A) (hbx : s.gpr .rbx = bP s₀) (h13 : s.gpr .r13 = sc s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩)
    (hAs : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩) (hAn : A.toNat + 128 * rr s₀ ≤ 2 ^ 64)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (bP s₀) (128 * rr s₀) = blockMix (rr s₀) (bytesAt s.mem A (128 * rr s₀)) →
      Q s') :
    WP isa (.block bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → f.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [uf.other _ h4, ue.other _ h3, ud.other _ h2, ub.other _ h1, ua.other _ h1]
  have hsi : b.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ub.gpr, ua.gpr, h14, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, ub.mem, ua.mem]
  have hsp' : f.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by decide) (by decide) (by decide) (by decide), hsp]
  refine hS f A (bP s₀) (sc s₀) (rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide) (by decide), hA])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi])
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), hbx])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi])
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h13])
    hp.pos lt ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hAb hAw
    (by rw [hsp']; exact hAs) (by rw [hsp']; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [hsp']; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hAn (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega)
    (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hrd, hwr]; exact hAi)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact b_in hp)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact w_in hp) _
    fun s' rd' wr' cs' f' b' => hQ s' (by rw [rd', uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [wr', uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      (fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := calleeSaved_tail hr
        rw [cs' r hr, k r h1 h2 h3 h4])
      (by rw [hm, hsp'] at f'; exact f') (by rw [b', hm])

/-! ## Step 2 -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < NN s₀) : (vAt s₀ i).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := v_lt hp
  have := hp.pos
  have hv := hp.v_nw
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [Memory.toNat_add_ofNat _ (by omega)]
  omega

theorem vAt_in {i : Nat} (hi : i < NN s₀) : InRegions s₀.wr (vAt s₀ i) (128 * rr s₀) := by
  rw [hp.wr]
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have lt := v_lt hp
  exact Memory.InRegions.of_mem (R := vR s₀) (by simp)
    (Memory.contains_off (by rw [e]; omega) (by omega))

/-- `V[i]` and the parts of `scratch` and the stack we use. -/
theorem vAt_b {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (bR s₀) :=
  hp.b_v.symm.sub_left (vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (scR s₀) :=
  hp.v_s.sub_left (vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < NN s₀) : Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ (stkR s₀) :=
  hp.stk_v.symm.sub_left (vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m') :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨bR s₀, by simp, b_sub'⟩
    · exact ⟨scR s₀, by simp, w_sub⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `V[k]`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    {k : Nat} (hk : k < NN s₀) :
    bytesAt m' (vAt s₀ k) (128 * rr s₀) = bytesAt m (vAt s₀ k) (128 * rr s₀) := by
  refine frame_bytesAt' hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (vAt_b hp hk).sub_right b_sub'
  · exact (vAt_s hp hk).sub_right w_sub
  · exact vAt_stk hp hk

theorem call_kept {m m' : Mem} (hf : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀] m m')
    (h : Kept s₀ m) : Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (keep_b hp).sub_right b_sub'
    · exact keep_w
    · exact keep_stk hp

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) m₃)
    (b₃ : bytesAt m₃ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
        (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₃ ∧ Kept s₀ m₃ ∧
    bytesAt m₃ (bP s₀) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) (i + 1) (B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) := by
  have lt := r_lt hp
  have hl : (bytesAt s.mem (bP s₀) (128 * rr s₀)).length = 128 * rr s₀ := Memory.bytesAt_length _ _ _
  have hself : bytesAt (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) (vAt s₀ i)
      (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) i (B s₀) := by
    have := Memory.bytesAt_writeBytes_self s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))
      (by rw [hl]; exact lt)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨vAt s₀ i, 128 * rr s₀⟩] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem
      (writeBytes s.mem (vAt s₀ i) (bytesAt s.mem (bP s₀) (128 * rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨vR s₀, by simp, vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (call_frame f₃), call_kept hp f₃ (h.kept.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (keep_v hp).sub_right (vAt_sub hp hi)
  · rw [call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [Memory.bytesAt_writeBytes_sep _ _ (by rw [hl]; exact vAt_disj hp (by omega) hi hki) lt]
      exact h.done k (by omega)

end

theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem vAt_succ (s₀ : State) (i : Nat) :
    vAt s₀ i + BitVec.ofNat 64 (128 * rr s₀) = vAt s₀ (i + 1) := by
  show _ = vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * (i + 1))
  rw [Memory.add_ofNat, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (bP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := r_lt hp
  rw [hp.rd, hp.wr]
  exact Memory.InRegions.of_mem (R := bR s₀) (by simp) (Memory.contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : Pre s₀) {i k : Nat} (hi : i < NN s₀) (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (vAt s₀ i + BitVec.ofNat 64 (8 * k)) 8 := by
  rw [hp.wr]
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have lt := v_lt hp
  show InRegions _ (vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i) + BitVec.ofNat 64 (8 * k)) 8
  rw [Memory.add_ofNat]
  exact Memory.InRegions.of_mem (R := vR s₀) (by simp)
    (Memory.contains_off (by rw [e]; omega) (by omega))

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => Inv2 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  have lt := r_lt hp
  have vlt := v_lt hp
  have pos := hp.pos
  have n1 := NN_pos hp
  have hN : NN s₀ < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold step2
  refine WP.seq (wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → e.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ue.other _ h3, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : e.rd = s₀.rd := by rw [ue.rd, ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : e.wr = s₀.wr := by rw [ue.wr, ud.wr, ub.wr, ua.wr, h.wr]
  have hme : e.mem = s.mem := by rw [ue.mem, ud.mem, ub.mem, ua.mem]
  have ecx : e.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀) := by
    rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.seq (WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ i) (n := 16 * rr s₀) (by omega)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.gpr, h.rbx])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp])
    ecx (fun k hk => by rw [erd, ewr]; exact b_word hp hk)
    (fun k hk => by rw [ewr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub'))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [hme, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := cs_ne hr
    rw [gt r h1 h2 h3 h4, ke r h2 h3 h4]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun f uf _ _ => ?_))
  have kf : ∀ r ∈ calleeSaved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (cs_ne hr).2.1, kt r hr]
  have cs : ∀ r ∈ calleeSaved, r ∈ calleeSaved := fun _ h => h
  refine bm_ok hS hp (A := vAt s₀ i) (by rw [uf.gpr, kt _ (by simp [calleeSaved]), h.rbp])
    (by rw [kf _ (by simp [calleeSaved]), h.rbx]) (by rw [kf _ (by simp [calleeSaved]), h.r13])
    (by rw [kf _ (by simp [calleeSaved]), h.r14]) (by rw [kf _ (by simp [calleeSaved]), h.rsp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr])
    ((vAt_b hp hi).sub_right b_sub') ((vAt_s hp hi).sub_right w_sub) (vAt_stk hp hi).symm
    (vAt_nw hp hi) (Memory.InRegions.right (vAt_in hp hi)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  obtain ⟨F, K, X, D⟩ := mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kf r hr]
  refine wp_add fun s5 u5 => wp_subi fun s6 u6 z6 => WP.block_nil ?_
  have k6 : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .r15 → s6.gpr r = s.gpr r := fun r hr h1 h2 => by
    rw [u6.other _ h2, u5.other _ h1, k4 r hr]
  have e15 : s5.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i) := by
    rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]), h.r15]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.rsp],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.rbx], ?_,
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r12],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r13],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r14],
    by rw [u6.gpr, e15, dec_count hi],
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, k4 _ (by simp [calleeSaved]), k4 _ (by simp [calleeSaved]),
      h.rbp, h.r14, vAt_succ]
  · rw [z6, e15, dec_zf hi hN]

theorem loop2_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (Inv2 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv2 s₀) (fun _ hi _ h => step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = BitVec.ofNat 64 (NN s₀ - 1)
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i)
  frame : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  kept : Kept s₀ s.mem
  v : ∀ k < NN s₀, bytesAt s.mem (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)
  x : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - i)
    (bytesAt s.mem (bP s₀) (128 * rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv2 s₀ (NN s₀) s) :
    WP isa (.block rmMid) s (Inv3 s₀ 0) := by
  have n1 := NN_pos hp
  unfold rmMid
  refine wp_movm (a := sc s₀ + BitVec.ofNat 64 176) (by rw [BlockMix.ea_at, h.r13])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega)))
    fun a ua => wp_mov fun b ub _ _ => wp_subi fun d ud _ => WP.block_nil ?_
  have ka : a.gpr .r15 = BitVec.ofNat 64 (NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .r15 → r ≠ .rbp → d.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ud.other _ h2, ub.other _ h2, ua.other _ h1]
  have hm : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ud.rd, ub.rd, ua.rd, h.rd], by rw [ud.wr, ub.wr, ua.wr, h.wr],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx], ?_,
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [ud.other _ (by decide), ub.other _ (by decide), ka]; rfl,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk, ?_,
    ?_⟩
  · rw [ud.gpr, ub.gpr, ka]
    have := dec_count (n := NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem ea_j {s₀ : State} (hp : Pre s₀) (s : State) (hbx : s.gpr .rbx = bP s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)) :
    s.ea { base := .rbx, index := some .r14, disp := -64 } =
      bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64) := by
  have := hp.pos
  simp only [State.ea, hbx, h14]
  rw [ofNat_split (a := 64) (b := 128 * rr s₀) (by omega),
    show BitVec.ofInt 64 (-64) = 0 - BitVec.ofNat 64 64 by decide]
  bv_omega

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (rr s₀) (bytesAt m (bP s₀) (128 * rr s₀)) % NN s₀

theorem jOf_lt {s₀ : State} (hp : Pre s₀) (m : Mem) : jOf s₀ m < NN s₀ :=
  Nat.mod_lt _ (NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : Pre s₀) (m : Mem) :
    m.readW (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 &&& BitVec.ofNat 64 (NN s₀ - 1) =
      BitVec.ofNat 64 (jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have vlt := v_lt hp
  have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  have he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [Memory.toNat_ofNat_lt (by have := jOf_lt hp m; omega), he, and_mask _ he', jOf, he,
    integerify_mod _ _ hp.pos he']

theorem t_word {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 16 * rr s₀) :
    InRegions s₀.wr (tP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := hp.s_nw
  rw [hp.wr, Memory.add_ofNat]
  exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (Memory.contains_off (by omega) (by omega))

theorem t_in {s₀ : State} (hp : Pre s₀) : InRegions s₀.wr (tP s₀) (128 * rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (Memory.contains_off (by omega) (by omega))

theorem t_b {s₀ : State} (hp : Pre s₀) :
    Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩ :=
  (hp.b_s.symm.sub_left (t_sub hp)).sub_right b_sub'

theorem t_nw {s₀ : State} (hp : Pre s₀) : (tP s₀).toNat + 128 * rr s₀ ≤ 2 ^ 64 := by
  have := hp.s_nw
  rw [Memory.toNat_add_ofNat _ (by omega)]
  omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩, stkR s₀]
      (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (bP s₀) (128 * rr s₀) = blockMix (rr s₀)
      (bytesAt (writeBytes s.mem (tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
        (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)))) (tP s₀) (128 * rr s₀))) :
    Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s₀.mem m₄ ∧ Kept s₀ m₄ ∧
    (∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀)) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).1 = roMix (rr s₀) (NN s₀) (B s₀) ∧
    (Spec.Scrypt.mixLoop (rr s₀) (NN s₀) (vList (rr s₀) (NN s₀) (B s₀)) (NN s₀ - (i + 1))
      (bytesAt m₄ (bP s₀) (128 * rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop (i + 1) := by
  have lt := r_lt hp
  have hj := jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (bP s₀) (128 * rr s₀))
    (bytesAt s.mem (vAt s₀ (jOf s₀ s.mem)) (128 * rr s₀)) with hT
  have hl : T.length = 128 * rr s₀ := by
    rw [hT, Memory.xorBytes_length _ _ (by simp [Memory.bytesAt_length]), Memory.bytesAt_length]
  have hself : bytesAt (writeBytes s.mem (tP s₀) T) (tP s₀) (128 * rr s₀) = T := by
    have := Memory.bytesAt_writeBytes_self s.mem (tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  have f₂ : Frame [⟨tP s₀, 128 * rr s₀⟩] s.mem (writeBytes s.mem (tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [bR s₀, vR s₀, scR s₀, stkR s₀] s.mem (writeBytes s.mem (tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, t_sub hp⟩
  have hv : ∀ k < NN s₀, bytesAt m₄ (vAt s₀ k) (128 * rr s₀) = Nat.repeat (blockMix (rr s₀)) k (B s₀) :=
    fun k hk => by
      rw [call_keeps_v hp f₄ hk, Memory.bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (vAt_s hp hk).sub_right (t_sub hp)) lt]
      exact h.v k hk
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (call_frame f₄),
    call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

theorem sx192 : (192 : BitVec 32).signExtend 64 = BitVec.ofNat 64 192 := by decide

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {i : Nat}
    (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => Inv3 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀)) := by
  have lt := r_lt hp
  have vlt := v_lt hp
  have pos := hp.pos
  have hN : NN s₀ < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hj := jOf_lt hp s.mem
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  have hrd : s.rd = s₀.rd := h.rd
  have hwr : s.wr = s₀.wr := h.wr
  unfold step3 jBlock
  refine WP.seq (wp_movm (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) (ea_j hp s h.rbx h.r14)
    (by rw [hrd, hwr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := bR s₀) (by simp)
          (Memory.contains_off (by omega) (by omega)))
    fun a ua => wp_and fun b ub => WP.block_nil ?_)
  have hax : b.gpr .rax = BitVec.ofNat 64 (jOf s₀ s.mem) := by
    rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp]; exact jOf_eq hp s.mem
  refine WP.seq (wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (mulLoop_ok (j := jOf s₀ s.mem) (c := 128 * rr s₀) (a := vP s₀)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), hax])
    (by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r12])
    (by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14]))
    fun f ⟨rdf, wrf, mf, gf, dxf⟩ => ?_)
  have hdx : f.gpr .rdx = vAt s₀ (jOf s₀ s.mem) := by rw [dxf, Nat.mul_comm]
  refine WP.seq (wp_mov fun g1 u1 _ _ => wp_mov fun g2 u2 _ _ => wp_mov fun g3 u3 _ _ =>
    wp_addi fun g4 u4 => wp_mov fun g5 u5 _ _ => wp_shr (by decide) (by decide) fun g6 u6 _ =>
    WP.block_nil ?_)
  have rd6 : g6.rd = s₀.rd := by
    rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, rdf, ue.rd, ud.rd, ub.rd, ua.rd, hrd]
  have wr6 : g6.wr = s₀.wr := by
    rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, wrf, ue.wr, ud.wr, ub.wr, ua.wr, hwr]
  have m6 : g6.mem = s.mem := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, mf, ue.mem, ud.mem, ub.mem, ua.mem]
  have k6 : ∀ r ∈ calleeSaved, g6.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cs_ne hr
    rw [u6.other _ h4, u5.other _ h4, u4.other _ h6, u3.other _ h6, u2.other _ h3, u1.other _ h2,
      gf _ h1 h5 h4, ue.other _ h4, ud.other _ h5, ub.other _ h1, ua.other _ h1]
  have x6 : g6.gpr .r8 = tP s₀ := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13, sx192]
  refine WP.seq (WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ (jOf s₀ s.mem)) (d := tP s₀)
    (n := 16 * rr s₀) (by omega) (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, gf _ (by decide) (by decide) (by decide),
      ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide),
      h.rbx])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hdx])
    x6
    (by rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14,
      shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega))
    (fun k hk => by rw [rd6, wr6]; exact b_word hp hk)
    (fun k hk => by rw [rd6, wr6]; exact Memory.InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [wr6]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [m6, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := cs_ne hr
    rw [gt r h1 h2 h3 h6 h4, k6 r hr]
  rw [blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun q1 v1 _ _ => wp_addi fun q2 v2 => ?_))
  have kq : ∀ r ∈ calleeSaved, q2.gpr r = s.gpr r := fun r hr => by
    rw [v2.other _ (cs_ne hr).2.1, v1.other _ (cs_ne hr).2.1, kt r hr]
  refine bm_ok hS hp (A := tP s₀)
    (by rw [v2.gpr, v1.gpr, kt _ (by decide), h.r13, sx192])
    (by rw [kq _ (by decide), h.rbx]) (by rw [kq _ (by decide), h.r13])
    (by rw [kq _ (by decide), h.r14]) (by rw [kq _ (by decide), h.rsp])
    (by rw [v2.rd, v1.rd, rdt, rd6]) (by rw [v2.wr, v1.wr, wrt, wr6])
    (t_b hp) (t_w hp) (hp.stk_s.sub_right (t_sub hp)) (t_nw hp)
    (Memory.InRegions.right (t_in hp)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [v2.mem, v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kq r hr]
  refine wp_subi fun s5 u5 z5 => WP.block_nil ?_
  have k5 : ∀ r ∈ calleeSaved, r ≠ .r15 → s5.gpr r = s.gpr r := fun r hr h1 => by
    rw [u5.other _ h1, k4 r hr]
  have e15 : s4.gpr .r15 = BitVec.ofNat 64 (NN s₀ - i) := by rw [k4 _ (by decide), h.r15]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v2.rd, v1.rd, rdt, rd6],
    by rw [u5.wr, wr4, v2.wr, v1.wr, wrt, wr6],
    by rw [k5 _ (by decide) (by decide), h.rsp], by rw [k5 _ (by decide) (by decide), h.rbx],
    by rw [k5 _ (by decide) (by decide), h.rbp], by rw [k5 _ (by decide) (by decide), h.r12],
    by rw [k5 _ (by decide) (by decide), h.r13], by rw [k5 _ (by decide) (by decide), h.r14],
    by rw [u5.gpr, e15, dec_count hi],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [z5, e15, dec_zf hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (Inv3 s₀ (NN s₀)) :=
  count_loop (NN_pos hp) (Inv3 s₀) (fun _ hi _ h => step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv3 s₀ (NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  refine WP.mono (Spill.restore_ok .r13 rmSaved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r13]; exact h.kept.1)) fun s' ⟨h₁, h₂, hm, _⟩ =>
    ⟨hm, Spill.calleeSaved_ok h₁ h₂ (by decide) h.rsp⟩
  have := saved_offs hp'
  rw [h.r13, h.rd, h.wr, hp.rd, hp.wr]
  exact Memory.InRegions.of_mem (R := scR s₀) (by simp) (in_s s₀ (by omega))

/-! ## The whole function -/

theorem correct {c : Prog isa} (hS : BlockMixSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.roMixX86_64.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine start_ok hp h₁ fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop2_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (mid_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (loop3_ok hS hp h₄) fun s₅ h₅ => ?_)
  refine WP.mono (restore_ok hp h₅) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₅.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_b
    · exact hp.ret_v
    · exact hp.ret_s
    · exact ret_stk s₀
  · show bytesAt s'.mem (bP s₀) (128 * rr s₀) = roMix (rr s₀) (NN s₀) (B s₀)
    rw [hm', ← h₅.x, Nat.sub_self]
    rfl

end VG.Proof.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: constant time, up to the indices `j`

As for scryptBlockMix (`BlockMixCT.lean`), we relate two runs (`RelCT`):
correctness determines our registers from the public arguments, so they
agree between the calls, where the taint analysis proves each block
constant time; the calls are constant time by scryptBlockMix's own proof.
In step 3, the address of `V[j]` and the branches of the multiplication
depend on `j`, which the contract declares public: the two runs compute the
same `j`, since both compute their indices in order (`Inv3.js`) and agree on
the whole list.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_add wp_subi)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.rsi]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.rsi, hq.rcx]
theorem PubEq.vAt (i : Nat) : vAt s₀ i = vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.rsi, hq.rdx]
theorem PubEq.tP : tP s₀ = tP s₀' := by simp only [RoMix.tP, RoMix.sc, hq.r8]

end

/-- The registers the loops keep, with `rbp = bp` and `r15 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = bP s₀
  rbp : s.gpr .rbp = bp
  r12 : s.gpr .r12 = vP s₀
  r13 : s.gpr .r13 = sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * rr s₀)
  r15 : s.gpr .r15 = q

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hk _ (by simp [calleeSaved])).trans h.rsp,
    (hk _ (by simp [calleeSaved])).trans h.rbx, (hk _ (by simp [calleeSaved])).trans h.rbp,
    (hk _ (by simp [calleeSaved])).trans h.r12, (hk _ (by simp [calleeSaved])).trans h.r13,
    (hk _ (by simp [calleeSaved])).trans h.r14, (hk _ (by simp [calleeSaved])).trans h.r15⟩

/-- `KR` survives instructions that write none of its registers. -/
theorem KR.upd {s₀ : State} {bp q : Addr} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) :
    KR s₀ bp q s' :=
  h.keep hrd hwr fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cs_ne hr
    exact hk r h1 h2 h3 h4 h5 h6

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) (BitVec.ofNat 64 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- The registers `KR` fixes agree in two runs. -/
theorem KR.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, bP, bP, hq.rdi]
  · rw [h.rbp, h'.rbp, hbp]
  · rw [h.r12, h'.r12, vP, vP, hq.rdx]
  · rw [h.r13, h'.r13, sc, sc, hq.r8]
  · rw [h.r14, h'.r14, hq.rr]
  · rw [h.r15, h'.r15, hq']
  · rw [h.rsp, h'.rsp, hq.rsp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  rdi : s.gpr .rdi = A
  rsi : s.gpr .rsi = BitVec.ofNat 64 (rr s₀)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (rr s₀)
  rdx : s.gpr .rdx = bP s₀
  r8 : s.gpr .r8 = sc s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨bP s₀, 128 * rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * rr s₀⟩ ⟨sc s₀, 128⟩
  stk : (stkR s₀).Disjoint ⟨A, 128 * rr s₀⟩
  nw : A.toNat + 128 * rr s₀ ≤ 2 ^ 64
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * rr s₀)

theorem srcOK_v {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) : SrcOK s₀ (vAt s₀ i) :=
  ⟨(vAt_b hp hi).sub_right b_sub', (vAt_s hp hi).sub_right w_sub, (vAt_stk hp hi).symm,
    vAt_nw hp hi, Memory.InRegions.right (vAt_in hp hi)⟩

theorem srcOK_t {s₀ : State} (hp : Pre s₀) : SrcOK s₀ (tP s₀) :=
  ⟨t_b hp, t_w hp, hp.stk_s.sub_right (t_sub hp), t_nw hp, Memory.InRegions.right (t_in hp)⟩

/-! ## The call -/

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixX86_64.pre (s.callEntry.withRegions [⟨A, 128 * rr s₀⟩]
      [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) ∧
    Covers ([⟨A, 128 * rr s₀⟩] ++ [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  exact bm_pre ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : Addr} (hA : SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMix) s (KR s₀ bp q) := by
  have lt := r_lt hp
  exact blockMixSpec s A (bP s₀) (sc s₀) (rr s₀) ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp) _ fun _ rd wr cs _ _ => h.keep rd wr cs

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀') {A A' : Addr}
    (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A') {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMix)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.rdi.symm
  have es : sc s₀' = sc s₀ := hq.r8.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    BlockMix.blockMix_correct BlockMix.blockMix_ct [⟨A, 128 * rr s₀⟩]
    [⟨bP s₀, 128 * rr s₀⟩, ⟨sc s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [h.rsp, h'.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8,
        ha'.rdi, ha'.rsi, ha'.rdx, ha'.rcx, ha'.r8, eb, es, er, h.rsp, h'.rsp, hq.rsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## What each piece does to the registers -/

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    X86_64.Taint.Agree (Taint.ofRegs (extra ++ kRegs)) s s' :=
  Taint.agree_ofRegs fun r hr => (List.mem_append.mp hr).elim (hx r) (KR.agree hq h h' hbp hq' r)

theorem a2_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
      .shift .shr .rcx 3]) s fun s' => KR s₀ bp q s' ∧ s'.gpr .rdi = bP s₀ ∧ s'.gpr .rsi = bp ∧
        s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ h2 h3 h4 _ _ => by rw [ue.other _ h4, ud.other _ h4, ub.other _ h3, ua.other _ h2]
  · rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp]
  · rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega

theorem copy_wp {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < NN s₀) {q : Addr} {s : State}
    (h : KR s₀ (vAt s₀ i) q s) (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = vAt s₀ i)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) :
    WP isa copyLoop s (KR s₀ (vAt s₀ i) q) := by
  have lt := r_lt hp
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.mono (copyLoop_ok (src := bP s₀) (dst := vAt s₀ i) (n := 16 * rr s₀)
    (by have := hp.pos; omega) (by omega) hdi hsi hcx
    (fun k hk => by rw [h.rd, h.wr]; exact b_word hp hk)
    (fun k hk => by rw [h.wr]; exact v_word hp hi hk)
    (by rw [e8]; exact (vAt_b hp hi).symm.sub_left b_sub')) fun t ⟨rd, wr, g, _⟩ =>
    h.upd rd wr fun r h1 h2 h3 h4 _ _ => g r h1 h2 h3 h4

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : Addr} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .rdi = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ _ h3 h4 h5 h6 => by
        rw [uf.other _ h6, ue.other _ h5, ud.other _ h4, ub.other _ h3, ua.other _ h3]
  have hsi : b.gpr .rsi = BitVec.ofNat 64 (rr s₀) := by
    rw [ub.gpr, ua.gpr, h.r14, shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  exact ⟨by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi],
    by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.rbx],
    by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13]⟩

theorem x2_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block (([.mov .rdi (.reg .rbp)] : List Instr) ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mov fun a ua _ _ => tail_wp hp (h.upd ua.rd ua.wr fun r _ h2 _ _ _ _ => ua.other r h2)
    (by rw [ua.gpr, h.rbp])

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : Addr} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block (([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] : List Instr) ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP s₀) s' :=
  wp_mov fun a ua _ _ => wp_addi fun b ub => tail_wp hp
    (h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ h2 _ _ _ _ => by
      rw [ub.other r h2, ua.other r h2])
    (by rw [ub.gpr, ua.gpr, h.r13, sx192])

/-! ## Step 2, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv2 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt s₀ i = vAt s₀' i := hq.vAt i
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  have a : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
        .shift .shr .rcx 3]) fun s s' =>
        (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧ s.gpr .rdi = bP s₀ ∧
          s.gpr .rsi = vAt s₀ i ∧ s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' ∧ s'.gpr .rdi = bP s₀' ∧
          s'.gpr .rsi = vAt s₀' i ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨a2_wp hp h.1.kr, a2_wp hp' h.2.kr⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have c : RelCT isa (fun s s' =>
        (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧ s.gpr .rdi = bP s₀ ∧
          s.gpr .rsi = vAt s₀ i ∧ s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' ∧ s'.gpr .rdi = bP s₀' ∧
          s'.gpr .rsi = vAt s₀' i ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')))
      copyLoop fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, d, si, cx⟩, ⟨h', d', si', cx'⟩⟩ => agree_K hq h h' ev e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [d, d', bP, bP, hq.rdi]
        · rw [si, si', ev]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, d, si, cx⟩, ⟨h', d', si', cx'⟩⟩ =>
        ⟨copy_wp hp hi h d si cx, copy_wp hp' hi' h' d' si' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have x : RelCT isa (fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s')
      (.block ([.mov .rdi (.reg .rbp)] ++ bmTail)) fun s s' =>
        (KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧ Args s₀ (vAt s₀ i) s) ∧
        (KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s' ∧ Args s₀' (vAt s₀' i) s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x2_wp hp h.1, x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt s₀ i) (q := BitVec.ofNat 64 (NN s₀ - i)) (bp' := vAt s₀' i)
    (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => KR s₀ (vAt s₀ i) (BitVec.ofNat 64 (NN s₀ - i)) s ∧
        KR s₀' (vAt s₀' i) (BitVec.ofNat 64 (NN s₀' - i)) s')
      (.block [.alu .add .rbp (.reg .r14), .alu .sub .r15 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := a.seq (c.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s') (.loop (step2 Impl.Scrypt.X86_64.blockMix) .ne)
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.X86_64.blockMix) (c := .ne)
    (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3: what each piece does to the registers -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : Addr} {s : State}
    (h : KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 64 (NN s₀ - 1)) q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j := by
  have lt := r_lt hp
  have := hp.pos
  unfold jBlock
  refine Proof.MdStream.X86_64.wp_movm (a := bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64))
    (ea_j hp s h.rbx h.r14)
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := bR s₀) (by simp)
          (Memory.contains_off (by omega) (by omega)))
    fun a ua => wp_and fun b ub => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r h1 _ _ _ _ _ => by
      rw [ub.other _ h1, ua.other _ h1]
  · rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp, jOf_eq hp, hj]

theorem m1_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) {j : Nat}
    (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) s fun s' =>
      KR s₀ bp q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀) :=
  wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => WP.block_nil
    ⟨h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ _ _ h4 h5 _ => by
      rw [ub.other _ h4, ua.other _ h5],
    by rw [ub.other _ (by decide), ua.other _ (by decide), hax],
    by rw [ub.other _ (by decide), ua.gpr, h.r12], by rw [ub.gpr, ua.other _ (by decide), h.r14]⟩

theorem mul_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) {j : Nat} (hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = vP s₀)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) :
    WP isa mulLoop s fun s' => KR s₀ bp q s' ∧ s'.gpr .rdx = vAt s₀ j :=
  WP.mono (mulLoop_ok hj hax hdx hcx) fun _ ⟨rd, wr, _, g, dx⟩ =>
    ⟨h.upd rd wr fun r h1 _ _ h4 h5 _ => g r h1 h5 h4, by rw [dx, Nat.mul_comm]⟩

theorem m2_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) (hp : Pre s₀) {j : Nat}
    (hdx : s.gpr .rdx = vAt s₀ j) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
      .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) s fun s' =>
      KR s₀ bp q s' ∧ s'.gpr .rdi = bP s₀ ∧ s'.gpr .rsi = vAt s₀ j ∧ s'.gpr .r8 = tP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀) := by
  have lt := r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ => wp_addi fun e ue =>
    wp_mov fun f uf _ _ => wp_shr (by decide) (by decide) fun g ug _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ug.rd, uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [ug.wr, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr]) fun r _ h2 h3 h4 _ h6 => by
        rw [ug.other _ h4, uf.other _ h4, ue.other _ h6, ud.other _ h6, ub.other _ h3, ua.other _ h2]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.gpr, ua.other _ (by decide), hdx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.gpr, ub.other _ (by decide),
      ua.other _ (by decide), h.r13, sx192]
  · rw [ug.gpr, uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r14, shr_ofNat _ lt]
    congr 1; omega

theorem xor_wp {bp q : Addr} {s₀ : State} {s : State} (h : KR s₀ bp q s) (hp : Pre s₀) {j : Nat}
    (hj : j < NN s₀) (hdi : s.gpr .rdi = bP s₀) (hsi : s.gpr .rsi = vAt s₀ j)
    (hr8 : s.gpr .r8 = tP s₀) (hcx : s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) :
    WP isa xorLoop s (KR s₀ bp q) := by
  have lt := r_lt hp
  have e8 : 8 * (16 * rr s₀) = 128 * rr s₀ := by omega
  refine WP.mono (xorLoop_ok (x := bP s₀) (y := vAt s₀ j) (d := tP s₀) (n := 16 * rr s₀)
    (by have := hp.pos; omega) (by omega) hdi hsi hr8 hcx
    (fun k hk => by rw [h.rd, h.wr]; exact b_word hp hk)
    (fun k hk => by rw [h.rd, h.wr]; exact Memory.InRegions.right (v_word hp hj hk))
    (fun k hk => by rw [h.wr]; exact t_word hp hk)
    (by rw [e8]; exact t_b hp) (by rw [e8]; exact (vAt_s hp hj).symm.sub_left (t_sub hp)))
    fun _ ⟨rd, wr, g, _⟩ => h.upd rd wr fun r h1 h2 h3 h4 _ h6 => g r h1 h2 h3 h6 h4

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Step 3, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) (hj : j < NN s₀) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have hj' : j < NN s₀' := hq.NN ▸ hj
  have vlt := v_lt hp
  have hjl : j < 2 ^ 64 := by
    have : NN s₀ ≤ 128 * rr s₀ * NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
    omega
  have e1 : BitVec.ofNat 64 (NN s₀ - 1) = BitVec.ofNat 64 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 64 (NN s₀ - i) = BitVec.ofNat 64 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop := KR t₀ (BitVec.ofNat 64 (NN t₀ - 1)) (BitVec.ofNat 64 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have m1 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j))
      (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide)).wp
      fun _ _ h => ⟨m1_wp h.1.1 h.1.2, m1_wp h.2.1 h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have ml : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * rr s₀')))
      mulLoop fun s s' => (K s₀ s ∧ s.gpr .rdx = vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = vAt s₀' j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax, .rdx, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ => agree_K hq h h' e1 e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ax, ax']
        · rw [dx, dx', vP, vP, hq.rdx]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ =>
        ⟨mul_wp h hjl ax dx cx, mul_wp h' hjl ax' dx' cx'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m2 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rdx = vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = vAt s₀' j))
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
        .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = bP s₀ ∧ s.gpr .rsi = vAt s₀ j ∧ s.gpr .r8 = tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = bP s₀' ∧ s'.gpr .rsi = vAt s₀' j ∧ s'.gpr .r8 = tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdx] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hq.vAt])
      (by taint_decide)).wp
      fun _ _ h => ⟨m2_wp h.1.1 hp h.1.2, m2_wp h.2.1 hp' h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have xl : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = bP s₀ ∧ s.gpr .rsi = vAt s₀ j ∧ s.gpr .r8 = tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = bP s₀' ∧ s'.gpr .rsi = vAt s₀' j ∧ s'.gpr .r8 = tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (16 * rr s₀')))
      xorLoop fun s s' => K s₀ s ∧ K s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .r8, .rcx] ++ kRegs))
      (fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ => agree_K hq h h' e1 e15
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [di, di', bP, bP, hq.rdi]
          · rw [si, si', hq.vAt]
          · rw [r8, r8', hq.tP]
          · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ =>
        ⟨xor_wp h hp hj di si r8 cx, xor_wp h' hp' hj' di' si' r8' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP s₀') s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (NN s₀ - 1)) (q := BitVec.ofNat 64 (NN s₀ - i))
    (bp' := BitVec.ofNat 64 (NN s₀' - 1)) (q' := BitVec.ofNat 64 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.alu .sub .r15 (.imm 1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (m1.seq (ml.seq (m2.seq (xl.seq ((x.seq cl).seq e)))))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Fin (NN s₀)) => body3_rel_j hp hp' hq hi j.1 j.2).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨⟨jOf s₀ s.mem, jOf_lt hp s.mem⟩, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s') (.loop (step3 Impl.Scrypt.X86_64.blockMix) .ne)
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.X86_64.blockMix) (c := .ne)
    (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.X86_64.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.X86_64.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rax, .rdx, .rcx])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rax, h'.rax, hq.rr]
        · rw [h.rdx, h'.rdx]
        · rw [h.rcx, h'.rcx, RoMix.vl, RoMix.vl, hq.rcx]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdx, .r12, .r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rdx, h'.rdx, hq.NN]
        · rw [h.r12, h'.r12, vP, vP, hq.rdx]
        · rw [h.r13, h'.r13, sc, sc, hq.r8]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.r13, h'.r13, sc, sc, hq.r8]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixX86_64.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .r9 => 3
    | .rsp => 0x5000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.roMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct blockMixSpec (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixX86_64.pre Proof.Scrypt.roMixX86_64.pub
    Impl.Scrypt.X86_64.roMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem roMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.roMix (Spec.Scrypt.roMixContract X86_64.abi 16) :=
  Verified.of_correct roMix_correct roMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.RoMix.satState]
          [Proof.Scrypt.X86_64.RoMix.satState] using Proof.Scrypt.X86_64.RoMix.satState }

end VG.Proof.Scrypt.X86_64.RoMix
