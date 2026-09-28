import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT
import VerifiedGarbage.Proof.Scrypt.RoMix
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: the precondition and the calls

Untrusted: everything here is checked by Lean. The regions the function
works on, and `BlockMixSpec`: what a call of the verified
`vg_scrypt_blockmix` does, from its `Verified` proof by `WP.call`.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

namespace Stream
export VG.Proof.Sha1.X86_64.Stream (Upd)
end Stream

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Scrypt.X86_64.BlockMix (covers_of_in covers_pair)
open VG.Proof.Sha1.X86_64.Stream (callEntry_byte)

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
  have : ((instrs Impl.Scrypt.X86_64.blockMix).all fun i => Taint.dstOf i != some .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  have := List.all_eq_true.mp this i hi
  simpa using this

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

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.X86_64.blockMix := by
  intro s src dst scr r hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr Q hQ
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have tr : (BitVec.ofNat 64 r).toNat = r := BlockMix.toNat_ofNat_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  refine WP.call (k := Proof.Scrypt.blockMixX86_64) BlockMix.blockMix_verified.1 blockMix_nosp
    (by rw [blockMix_depth]; decide) (rd := [⟨src, 128 * r⟩]) (wr := [⟨dst, 128 * r⟩, ⟨scr, 128⟩])
    ?_ ?_ ?_ ?_
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
  · have := covers_pair (covers_of_in idst) (covers_of_in iscr)
    have h1 := covers_of_in isrc
    intro a n h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h1 a n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨R', hR', hc'⟩ := this a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · obtain ⟨R', hR', hc'⟩ := this a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
  · exact covers_pair (covers_of_in idst) (covers_of_in iscr)
  · intro s₂ hrd hwr hcs hf _ ⟨s₃, hm₃, _, hpost⟩
    simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), hdi, hsi, hdx, hm₃, tr] at hpost
    rw [blockMix_depth] at hf
    refine hQ s₂ hrd hwr hcs (by simpa using hf) ?_
    rw [hpost]
    congr 1
    exact BlockMix.bytesAt_congr fun i hi =>
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
def Saved (m : Mem) : Prop :=
  ∀ p ∈ rmSaved, m.readW (sc s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

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
  have e : 128 * rr s₀ * NN s₀ = vl s₀ * 128 := by rw [hp.vl_eq]; ring_nf
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
  have e : vl s₀ * 128 = 128 * rr s₀ * NN s₀ := by rw [hp.vl_eq]; ring_nf
  have : 128 * rr s₀ * i + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  show Region.Sub ⟨vP s₀ + BitVec.ofNat 64 (128 * rr s₀ * i), 128 * rr s₀⟩ ⟨vP s₀, vl s₀ * 128⟩
  exact BlockMix.sub_off (by rw [e]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < NN s₀) (hk : k < NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨vAt s₀ i, 128 * rr s₀⟩ ⟨vAt s₀ k, 128 * rr s₀⟩ := by
  have := v_lt hp
  have hle : ∀ j, j < NN s₀ → 128 * rr s₀ * j + 128 * rr s₀ ≤ 128 * rr s₀ * NN s₀ := fun j hj => by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have h1 := hle i hi
  have h2 := hle k hk
  have hpos := hp.pos
  refine BlockMix.disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
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
  exact BlockMix.sub_off (by omega) (by omega)

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨sc s₀, 128⟩ (scR s₀) := Region.sub_prefix (by omega)

theorem t_w : Region.Disjoint ⟨tP s₀, 128 * rr s₀⟩ ⟨sc s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := BlockMix.disj_off (sc s₀) (o₁ := 192) (n₁ := 128 * rr s₀) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  BlockMix.contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  BlockMix.sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: the caller's registers and `N` -/

/-- Bytes `[128, 184)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨sc s₀ + BitVec.ofNat 64 128, 56⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  Saved s₀ m ∧ m.readW (sc s₀ + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 (NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 184) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 d, 8⟩ (keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← BlockMix.add_ofNat]
  exact BlockMix.sub_off (by omega) (by omega)

theorem saved_offs {p : Reg × Nat} (hp : p ∈ rmSaved) : 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 := by
  simp only [rmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

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
  have := BlockMix.disj_off (sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

theorem keep_t : (keepR s₀).Disjoint ⟨tP s₀, 128 * rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact BlockMix.disj_off (sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 192) (n₂ := 128 * rr s₀) (by omega)
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
  refine Proof.Sha1.X86_64.Stream.WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_ rfl)
  · simp [exec, execShift, h₁, h₂]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl,
      rfl⟩

theorem wp_and {d r : Reg}
    (k : ∀ s', Stream.Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.Sha1.X86_64.Stream.WP.cons rfl (k _ (VG.Proof.Sha1.X86_64.Stream.Upd.flags _ _ _ _ _ _))

end

theorem shr_ofNat {a : Nat} (n : Nat) (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BlockMix.toNat_ofNat_lt h, BlockMix.toNat_ofNat_lt
    (lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86_64.RoMix
