import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Gcm.Arm.Ghash
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.AesGcm.Arm

/-!
# AES-GCM on ARMv7: the functions called

Untrusted: everything here is checked by Lean. Each call, from its callee's
contract (with `WP.call`), with the regions it is given: what it needs
(`CtrCall`, `GhCall`, `KeyCall`) and what it leaves (`CtrPost`, `GhPost`,
`KeyPost`); and that it is constant time (`ctr_rel`, `gh_rel`, `key_rel`).
`vg_aes_ctr32` and `vg_ghash` are called in a frame that pushes their stack
arguments (`push {r12, lr}`) in the 8 bytes below the stack pointer.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-! ## Memory -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := Proof.Cmac.bytesAt_frame hf hd hn

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame hf hd hn]

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R :=
  toNat_ofNat32 (by omega)

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega)]
  omega

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- The 8 bytes below the stack pointer `sp`, where the frames push the stack
arguments. -/
abbrev below (sp : BitVec 32) : Region := ⟨State.addr sp - 8, 8⟩

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section Push
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub hsp

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [hspA hsp]; omega), hA hsp]; rfl

/-- The memory after `push {r12, lr}`. -/
theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [e8, storeWords_two, hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    hA4 hsp]

/-- The push writes only the 8 bytes below the stack pointer. -/
theorem fA : Frame [below s.sp] s.mem (pushed [.r12, .lr] s).mem := by
  rw [amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

omit hsp in
theorem pushed_sp8 : (pushed [.r12, .lr] s).sp = s.sp - 8 := by simp only [pushed_sp, e8]

/-- The stack arguments the push leaves. -/
theorem arg0 : stackArg (pushed [.r12, .lr] s) 0 = s.gpr .r12 := by
  rw [stackArg, show stackArgAddr (pushed [.r12, .lr] s) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [pushed_sp8, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, hA hsp],
    amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 : stackArg (pushed [.r12, .lr] s) 1 = s.gpr .lr := by
  rw [stackArg, show stackArgAddr (pushed [.r12, .lr] s) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [pushed_sp8]; exact hA4 hsp,
    amem hsp, Mem.readW_writeW_self32]

theorem argAddr0 : stackArgAddr (pushed [.r12, .lr] s) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [pushed_sp8, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
    BitVec.add_zero _, hA hsp]

/-- The register the pop loads is `r12`, as pushed, if the frame's body
changes nothing outside `rs`, which are apart from the 4 bytes below
the stack pointer's frame. -/
theorem popSlot {s₂ : State} {rs : List Region} (hf : Frame rs (pushed [.r12, .lr] s).mem s₂.mem)
    (hd : ∀ r ∈ rs, (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint r) :
    s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 := by
  rw [pushed_sp8, hA hsp, hf.readW (r := ⟨State.addr s.sp - 8, 4⟩) (a := State.addr s.sp - 8) (w := 32)
    (Region.contains_self _ _) hd (by decide), amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

end Push

@[simp] theorem stackArg_callEntry (s : State) (i : Nat) : stackArg s.callEntry i = stackArg s i := rfl
@[simp] theorem stackArgAddr_callEntry (s : State) (i : Nat) : stackArgAddr s.callEntry i = stackArgAddr s i := rfl

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem view_sp (s : State) (rd wr : List Region) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp8]

theorem view_mem (s : State) (rd wr : List Region) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).mem = (pushed [.r12, .lr] s).mem := by
  simp only [State.withRegions_mem, State.callEntry_mem]

theorem cover_pushed {s : State} {rs : List Region} (h : Covers rs s.wr) : Covers rs (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem cover_pushed' {s : State} {rs : List Region} (h : Covers rs (s.rd ++ s.wr)) :
    Covers rs ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h x n' hi
  refine ⟨r', ?_, hc'⟩
  rcases List.mem_append.mp hr' with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')

theorem pushed_wr8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (pushed [.r12, .lr] s).wr = ⟨State.addr s.sp - 8, 8⟩ :: s.wr := by
  rw [pushed_wr, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, show BitVec.ofNat 32 8 = 8 from rfl, hA hsp]

theorem cover_frame {s : State} (hsp : 8 ≤ s.sp.toNat) {n : Nat} (hn : n ≤ 8) :
    Covers [⟨State.addr s.sp - 8, n⟩] ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_append_right _ (by rw [pushed_wr8 hsp]; exact List.mem_cons_self ..), ?_⟩
  simp only [Region.Contains] at hc ⊢; omega

theorem covers_append' {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem ctr_noCalls : Impl.Aes.Arm.ctr32.noCalls = true := by decide +kernel
theorem gh_noCalls : Impl.Gcm.Arm.ghash.noCalls = true := by decide +kernel
theorem key_noCalls : Impl.Aes.Arm.expandKey.noCalls = true := by decide +kernel

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`,
with `n` in `r12` and `S` in `lr`, to push. -/
structure CtrCall (s : State) (K C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  fitK : K.toNat + 240 ≤ 2 ^ 32
  fitC : C.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 2048 ≤ 2 ^ 32
  kc : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  kd : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ks : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bk : (below s.sp).Disjoint ⟨State.addr K, 240⟩
  bc : (below s.sp).Disjoint ⟨State.addr C, 16⟩
  bd : (below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (below s.sp).Disjoint ⟨State.addr S, 2048⟩
  reads : Covers [⟨State.addr K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩, below s.sp] s.mem s'.mem
  out : blocksAt s'.mem (State.addr D) n =
    ctr32 (aesWith R (bytesAt s.mem (State.addr K) (16 * (R + 1)))) (blockAt s.mem (State.addr C))
      (blocksAt s.mem (State.addr D) n)
  ctr : blockAt s'.mem (State.addr C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (State.addr C))

abbrev ctrRd (sp K : BitVec 32) : List Region := [⟨State.addr K, 240⟩, below sp]
abbrev ctrWr (C D S : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩]

namespace CtrCall
variable {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : Proof.Aes.ctr32Arm.pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (ctrRd s.sp K) (ctrWr C D S n)) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  simp only [Proof.Aes.ctr32Arm, arg0 h.hsp, arg1 h.hsp, argAddr0 h.hsp, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, h.lr, hR, hn, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, view_sp, hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions, stackArg_callEntry,
    stackArgAddr_callEntry, arg0 h.hsp, arg1 h.hsp, argAddr0 h.hsp, h.r12, h.lr, hn]
  refine ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.bc.symm, h.bd.symm, h.bs.symm, h.fitK,
    h.fitC, h.fitD, h.fitS, ?_, h.rounds⟩
  have := s.sp.isLt; omega

theorem cov : Covers (ctrRd s.sp K ++ ctrWr C D S n)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (ctrWr C D S n) (pushed [.r12, .lr] s).wr := cover_pushed h.writes

end CtrCall

theorem ctr_call {s : State} {K C D S : BitVec 32} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa ctrFrame s (CtrPost s K C D S R n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct
    (rd := ctrRd s.sp K) (wr := ctrWr C D S n) h.pre h.cov h.covW ?_ ctr_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  have fA' := fA (s := s) h.hsp
  have bytesK : bytesAt (pushed [.r12, .lr] s).mem (State.addr K) (16 * (R + 1)) =
      bytesAt s.mem (State.addr K) (16 * (R + 1)) :=
    bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.symm.sub_left (Region.sub_prefix hR'))) (by omega)
  have blockC : blockAt (pushed [.r12, .lr] s).mem (State.addr C) = blockAt s.mem (State.addr C) :=
    blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bc.symm)
  have blocksD : blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n = blocksAt s.mem (State.addr D) n :=
    blocksAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm) (by have := h.fitD; omega)
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hR, stackArg_withRegions, stackArg_callEntry, arg0 h.hsp, h.r12, hn, bytesK, blockC, blocksD] at hdata hctr
  have fB : Frame (ctrWr C D S n) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.bc.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide))))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hdata
  · rw [popped_mem]; exact hctr

/-- Calls of `vg_aes_ctr32` with the same arguments and stack pointer in both
runs are constant time. -/
theorem ctr_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : BitVec 32, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ctrFrame fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct Proof.Aes.Arm.ctr32_ct
    (ctrRd s₁.sp K) (ctrWr C D S n) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Aes.ctr32Arm, stackArg_withRegions, stackArg_callEntry, arg0 h₁.hsp, arg1 h₁.hsp, arg0 h₂.hsp, arg1 h₂.hsp,
    view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide),
    view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, h₂.lr, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`, in `r12` to push. -/
structure GhCall (s : State) (H Y D S : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = H
  r1 : s.gpr .r1 = Y
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  fitH : H.toNat + 16 ≤ 2 ^ 32
  fitY : Y.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 256 ≤ 2 ^ 32
  hy : (⟨State.addr H, 16⟩ : Region).Disjoint ⟨State.addr Y, 16⟩
  hs : (⟨State.addr H, 16⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  yd : (⟨State.addr Y, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ys : (⟨State.addr Y, 16⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  bh : (below s.sp).Disjoint ⟨State.addr H, 16⟩
  by' : (below s.sp).Disjoint ⟨State.addr Y, 16⟩
  bd : (below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (below s.sp).Disjoint ⟨State.addr S, 256⟩
  reads : Covers [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩, below s.sp] s.mem s'.mem
  out : blockAt s'.mem (State.addr Y) =
    ghashFrom (blockAt s.mem (State.addr H)) (blockAt s.mem (State.addr Y)) (blocksAt s.mem (State.addr D) n)

abbrev ghRd (sp H D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr sp - 8, 4⟩]
abbrev ghWr (Y S : BitVec 32) : List Region := [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩]

namespace GhCall
variable {s : State} {H Y D S : BitVec 32} {n : Nat} (h : GhCall s H Y D S n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : Proof.Gcm.ghashArm.pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (ghRd s.sp H D n) (ghWr Y S)) := by
  have hn := toNat_ofNat32 h.n_lt
  have b4 : ∀ x : Region, (below s.sp).Disjoint x → (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint x :=
    fun x hx => hx.sub_left (Region.sub_prefix (by decide))
  simp only [Proof.Gcm.ghashArm, arg0 h.hsp, argAddr0 h.hsp, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, hn, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, view_sp, hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions, stackArg_callEntry,
    stackArgAddr_callEntry, arg0 h.hsp, arg1 h.hsp, argAddr0 h.hsp, h.r12, hn]
  refine ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, (b4 _ h.by').symm, (b4 _ h.bs).symm, h.fitH, h.fitY,
    h.fitD, h.fitS, ?_⟩
  have := s.sp.isLt; omega

theorem cov : Covers (ghRd s.sp H D n ++ ghWr Y S)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  have e : ghRd s.sp H D n = [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr s.sp - 8, 4⟩] := rfl
  rw [e]
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (ghWr Y S) (pushed [.r12, .lr] s).wr := cover_pushed h.writes

end GhCall

theorem gh_call {s : State} {H Y D S : BitVec 32} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa ghFrame s (GhPost s H Y D S n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Gcm.ghashArm) Proof.Gcm.Arm.ghash_correct
    (rd := ghRd s.sp H D n) (wr := ghWr Y S) h.pre h.cov h.covW ?_ gh_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hn := toNat_ofNat32 h.n_lt
  have fA' := fA (s := s) h.hsp
  have blockH : blockAt (pushed [.r12, .lr] s).mem (State.addr H) = blockAt s.mem (State.addr H) :=
    blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bh.symm)
  have blockY : blockAt (pushed [.r12, .lr] s).mem (State.addr Y) = blockAt s.mem (State.addr Y) :=
    blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.by'.symm)
  have blocksD : blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n = blocksAt s.mem (State.addr D) n :=
    blocksAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm) (by have := h.fitD; omega)
  simp only [Proof.Gcm.ghashArm, State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hn, blockH, blockY, blocksD] at hpost
  have fB : Frame (ghWr Y S) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.by'.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide))))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem gh_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S : BitVec 32, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ghFrame fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Gcm.ghashArm) Proof.Gcm.Arm.ghash_correct Proof.Gcm.Arm.ghash_ct
    (ghRd s₁.sp H D n) (ghWr Y S) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Gcm.ghashArm, stackArg_withRegions, stackArg_callEntry, arg0 h₁.hsp, arg0 h₂.hsp,
    view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide),
    view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : BitVec 32) (L : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 L
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  fitK : K.toNat + L ≤ 2 ^ 32
  fitC : C.toNat + 240 ≤ 2 ^ 32
  fitS : S.toNat + 512 ≤ 2 ^ 32
  kc : (⟨State.addr K, L⟩ : Region).Disjoint ⟨State.addr C, 240⟩
  ks : (⟨State.addr K, L⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  cs : (⟨State.addr C, 240⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  reads : Covers [⟨State.addr K, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KeyPost (s : State) (K C S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩] s.mem s'.mem
  out : bytesAt s'.mem (State.addr C) (16 * (Spec.Aes.rounds (L / 4) + 1)) =
    Spec.Aes.expandKey (bytesAt s.mem (State.addr K) L)

namespace KeyCall
variable {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L)
include h

theorem hL : (BitVec.ofNat 32 L).toNat = L :=
  toNat_ofNat32 (by rcases h.len with h' | h' | h' <;> omega)

theorem pre : Proof.Aes.expandKeyArm.pre
    (s.callEntry.withRegions [⟨State.addr K, L⟩] [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩]) := by
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
    h.r0, h.r1, h.r2, h.r3, h.hL]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.fitK, h.fitC, h.fitS, h.len⟩

end KeyCall

theorem key_call {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L) :
    WP isa (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) s (KeyPost s K C S L) := by
  refine WP.call (k := Proof.Aes.expandKeyArm) Proof.Aes.Arm.expandKey_correct
    (rd := [⟨State.addr K, L⟩]) (wr := [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩]) h.pre
    (covers_append' h.reads (fun x n' hi => by
      obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
      exact ⟨r', List.mem_append_right _ hr', hc'⟩)) h.writes ?_ key_noCalls
  intro s' hrd hwr hsp hf hcs _ hpost
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs), h.r0, h.r1, h.r2, h.hL] at hpost
  exact ⟨hrd, hwr, hsp, hcs, hf, hpost⟩

theorem key_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C S : BitVec 32, ∃ L : Nat, KeyCall s₁ K C S L ∧ KeyCall s₂ K C S L) :
    RelCT isa P (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, S, L, h₁, h₂⟩ := h _ _ hp
  have cov : ∀ {s : State}, KeyCall s K C S L →
      Covers ([⟨State.addr K, L⟩] ++ [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩]) (s.rd ++ s.wr) :=
    fun {s} hk => covers_append' hk.reads (fun x n' hi => by
      obtain ⟨r', hr', hc'⟩ := hk.writes x n' hi
      exact ⟨r', List.mem_append_right _ hr', hc'⟩)
  refine RelCT.call (k := Proof.Aes.expandKeyArm) Proof.Aes.Arm.expandKey_correct Proof.Aes.Arm.expandKey_ct
    [⟨State.addr K, L⟩] [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩] (P := fun x y => x = s₁ ∧ y = s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  refine ⟨h₁.pre, h₂.pre, ?_, cov h₁, h₁.writes, cov h₂, h₂.writes⟩
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.AesGcm.Arm
