import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hash
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.CallF

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: the calls of HMAC's functions and of `iterate`

As on x86 (`Proof/Pbkdf2/Whole/X86/Calls.lean`): `pbkdf2` calls HMAC's `init`
and `finalize` and PBKDF2's `iterate`, each verified against its shared
contract with 16 bytes of stack; what a caller uses of such a proof is
`Sound`. Each call is in a frame of two words, its stack arguments
(`frame2_ok`, with `WP.callF`, as the callees have frames of their own):
`hi_frame`, `hf_frame` and `it_frame` run one, from the state before its push,
given the registers (`HiArgs`, `HfArgs`, `ItArgs`), which give the callee's
precondition (evaluated with `sig_pre`); `hi_rel`, `hf_rel` and `it_rel`
relate two runs of one. Such a call writes only the 24 bytes below the stack
pointer (`stk`), which `After` lets change; so does a call of a streaming
function, in its frame of 16 bytes (`After.of_hmac`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Arm.FrameStack
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey hmacBlockKey)
open VG.Proof.Pbkdf2.Stream.Arm (ce0 ce1 ce2 ce3)
open Spec.Sha256 (bytesAt)

/-- What a caller uses of a proof of `Verified Arm.target c k`: that `c`
meets `k` and is constant time under it. -/
structure Sound (c : Prog isa) (k : Contract isa) : Prop where
  ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c

theorem Sound.of_verified {c : Prog isa} {k : Contract isa} (h : Verified Arm.target c k) : Sound c k :=
  ⟨h.1, h.2.1⟩

/-- `Sound` for a contract that asks no more and gives no less. -/
theorem Sound.weaken {c : Prog isa} {k k' : Contract isa} (h : Sound c k) (hpre : ∀ s, k'.pre s → k.pre s)
    (hpost : ∀ s s', k'.pre s → k.post s s' → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ → k.pub s₁ s₂) : Sound c k' :=
  ⟨fun s hs => (h.ok s (hpre s hs)).elim fun t ⟨s', he, ha, hp⟩ => ⟨t, s', he, ha, hpost s s' hs hp⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      h.ct s₁ s₂ t₁ t₂ s₁' s₂' (hpre _ h₁) (hpre _ h₂) (hpub _ _ h₁ h₂ hp) e₁ e₂⟩

/-! ## The stack below the stack pointer -/

/-- The 24 bytes below the stack pointer, where our frames and calls go. -/
abbrev stk (s : State) : Region := ⟨State.addr s.sp - 24, 24⟩

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and `stk`. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [stk s]) s.mem s'.mem

theorem stk_eq {s : State} (h : 24 ≤ s.sp.toNat) : belowA s.sp 24 = stk s := by
  simp only [belowA, addr_sub' h]; rfl

/-- `n` bytes below the stack pointer are in `stk`. -/
theorem below_stk {s : State} {n : Nat} (hn : n ≤ 24) :
    Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 n, n⟩ (stk s) :=
  fun x hx => Offset.below_mono _ (a := n) (b := 24) hn (by decide) x hx

/-- A call of a streaming function in its frame (`Proof/Pbkdf2/Stream/Arm/Hash.lean`). -/
theorem After.of_hmac {s s' : State} {ws : List Region}
    (h : Pbkdf2.Stream.Arm.After s ws s') : After s ws s' :=
  ⟨h.rd, h.wr, h.sp, h.cs, Frame.sub h.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_stk (s := s) (n := 16) (by decide)⟩⟩

/-- Two ranges below `p` that do not overlap. -/
theorem bdisj (p : Addr) (c : Nat) {a n b k : Nat} (ha : a ≤ c) (hb : b ≤ c)
    (h : c - a + n ≤ c - b ∨ c - b + k ≤ c - a) (hn : c + n < 2 ^ 32) (hk : c + k < 2 ^ 32) :
    Region.Disjoint ⟨p - BitVec.ofNat 64 a, n⟩ ⟨p - BitVec.ofNat 64 b, k⟩ := by
  rw [Offset.sub_ofNat_eq p ha, Offset.sub_ofNat_eq p hb]
  exact Offset.disjoint _ h (by omega) (by omega)

/-! ## A frame of two words around a call -/

section Frame2
variable {ra rb : Reg} {s : State}

theorem p2_mem :
    (pushed [ra, rb] s).mem = (s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 8)) (s.gpr ra)).writeW
      (State.addr (s.sp - BitVec.ofNat 32 8 + 4)) (s.gpr rb) := rfl

theorem p2_sp : (pushed [ra, rb] s).sp = s.sp - BitVec.ofNat 32 8 := rfl

theorem a8 (h : 8 ≤ s.sp.toNat) : State.addr (s.sp - BitVec.ofNat 32 8) = State.addr s.sp - BitVec.ofNat 64 8 :=
  addr_sub' h

theorem a84 (h : 8 ≤ s.sp.toNat) :
    State.addr (s.sp - BitVec.ofNat 32 8 + 4) = State.addr s.sp - BitVec.ofNat 64 8 + BitVec.ofNat 64 4 := by
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_add (by rw [sub_toNat' h]; have := s.sp.isLt; omega),
    a8 h]

theorem p2_arg0 (h : 8 ≤ s.sp.toNat) {rd wr : List Region} :
    stackArg ((pushed [ra, rb] s).callEntry.withRegions rd wr) 0 = s.gpr ra := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, p2_sp, Nat.mul_zero]
  rw [p2_mem, BitVec.add_zero, a84 h, a8 h,
    Mem.readW_writeW_sep (Pbkdf2.Stream.Arm.sep_base_off _ (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem p2_arg1 {rd wr : List Region} :
    stackArg ((pushed [ra, rb] s).callEntry.withRegions rd wr) 1 = s.gpr rb := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, p2_sp, Nat.mul_one]
  rw [p2_mem, show BitVec.ofNat 32 4 = (4 : BitVec 32) from rfl, Mem.readW_writeW_self32]

theorem p2_argAddr {rd wr : List Region} :
    stackArgAddr ((pushed [ra, rb] s).callEntry.withRegions rd wr) 0 = State.addr (s.sp - BitVec.ofNat 32 8) := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, p2_sp, Nat.mul_zero]
  rw [BitVec.add_zero]

omit ra rb in
/-- The frame's 8 bytes are in `stk`. -/
theorem p2_sub (h : 24 ≤ s.sp.toNat) : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ (stk s) := by
  rw [a8 (by omega)]; exact below_stk (by decide)

omit ra rb in
/-- The callee's 16 bytes below its stack pointer are in `stk`. -/
theorem p2_csub (h : 24 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8) - 16, 16⟩ (stk s) := by
  rw [a8 (by omega), BitVec.sub_sub, show BitVec.ofNat 64 8 + 16 = BitVec.ofNat 64 24 from rfl]
  exact Region.sub_prefix (by decide)

omit ra rb in
/-- And they are apart from the frame. -/
theorem p2_cdisj (h : 24 ≤ s.sp.toNat) {n : Nat} (hn : n ≤ 8) :
    Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 8) - 16, 16⟩ ⟨State.addr (s.sp - BitVec.ofNat 32 8), n⟩ := by
  rw [a8 (by omega), BitVec.sub_sub, show BitVec.ofNat 64 8 + 16 = BitVec.ofNat 64 24 from rfl]
  exact bdisj _ 24 (a := 24) (b := 8) (by decide) (by decide) (by omega) (by decide) (by omega)

end Frame2

/-- A frame of two words, popped into `t`, around a call of verified code
that uses at most 16 bytes of stack: the callee runs from the state after
the push, and the frame leaves `After`. -/
theorem frame2_ok {ra rb t : Reg} (hrs : regList [ra, rb] = true) (ht : t ∉ preserved)
    {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : armStack c ≤ 16) {s : State} (h24 : 24 ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed [ra, rb] s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed [ra, rb] s).rd ++ (pushed [ra, rb] s).wr))
    (hw : Covers wr (pushed [ra, rb] s).wr) {Q : State → Prop}
    (hQ : ∀ s₂ : State, After s wr (popped t 8 s₂) →
      k.post ((pushed [ra, rb] s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) → Q (popped t 8 s₂)) :
    WP isa (.frame (.push [ra, rb]) (.call n c) (.pop t 8)) s Q := by
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  refine WP.frame (rs := [ra, rb]) (r := t) hrs (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil]; omega) ?_
  refine WP.callF hv hpre hc hw (by rw [p2_sp, h8]; omega) fun s₂ hrd hwr hsp hf hcs hpost => ?_
  refine hQ s₂ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, p2_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ t := fun e => ht (e ▸ hr)
    rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    have f₀ := pushed_frameA (rs := [ra, rb]) (s := s) (by simp only [List.length_cons, List.length_nil]; omega)
    refine Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), p2_sub h24⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [p2_sp, ← stk_eq h24]
        exact belowA_inner (k := 8) (by omega) h24

/-- Two runs of such a frame leak the same, if their stack pointers are the
same and the callee's preconditions and public data hold. -/
theorem frame2_rel {ra rb t : Reg} (hrs : regList [ra, rb] = true) {n : String} {c : Prog isa}
    {k : Contract isa} (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧
      k.pre ((pushed [ra, rb] s₁).callEntry.withRegions rd wr) ∧
      k.pre ((pushed [ra, rb] s₂).callEntry.withRegions rd wr) ∧
      k.pub ((pushed [ra, rb] s₁).callEntry.withRegions rd wr) ((pushed [ra, rb] s₂).callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₁).rd ++ (pushed [ra, rb] s₁).wr) ∧ Covers wr (pushed [ra, rb] s₁).wr ∧
      Covers (rd ++ wr) ((pushed [ra, rb] s₂).rd ++ (pushed [ra, rb] s₂).wr) ∧ Covers wr (pushed [ra, rb] s₂).wr) :
    RelCT isa P (.frame (.push [ra, rb]) (.call n c) (.pop t 8)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h s₁ s₂ hp).1) (RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_)
  rw [Pbkdf2.Stream.Arm.push_eq hrs pa, Pbkdf2.Stream.Arm.push_eq hrs pb]
  exact (h s₁ s₂ hp).2

/-- The representation of a streaming state depends only on its bytes. -/
def ReprOK (S : StreamingHash) : Prop :=
  ∀ (m m' : Mem) (p q : Addr) (msg : List Byte),
    (∀ i < S.stateBytes, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → S.Repr m p msg → S.Repr m' q msg

/-- The memory on entry to a callee in a frame of two words is ours outside `stk`. -/
theorem p2_frame {ra rb : Reg} {s : State} (h24 : 24 ≤ s.sp.toNat) :
    Frame [stk s] s.mem (pushed [ra, rb] s).mem :=
  Frame.sub (pushed_frameA (rs := [ra, rb]) (s := s) (by simp only [List.length_cons, List.length_nil]; omega))
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, p2_sub h24⟩

theorem p2_bytes {ra rb : Reg} {s : State} (h24 : 24 ≤ s.sp.toNat) {p : Addr} {k : Nat}
    (hd : (stk s).Disjoint ⟨p, k⟩) (hk : k ≤ 2 ^ 64) :
    bytesAt (pushed [ra, rb] s).mem p k = bytesAt s.mem p k := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => (p2_frame h24).bytes (R := ⟨p, k⟩)
    (by simp only [List.mem_singleton]; rintro q rfl; exact hd.symm) hk (List.mem_range.mp hi)

theorem p2_repr {S : StreamingHash} (hR : ReprOK S) (hS : S.stateBytes ≤ 2 ^ 64) {ra rb : Reg} {s : State}
    (h24 : 24 ≤ s.sp.toNat) {p : Addr} (hd : (stk s).Disjoint ⟨p, S.stateBytes⟩) {msg : List Byte}
    (h : S.Repr s.mem p msg) : S.Repr (pushed [ra, rb] s).mem p msg :=
  hR _ _ _ _ _ (fun i hi => (p2_frame h24).bytes (R := ⟨p, S.stateBytes⟩)
    (by simp only [List.mem_singleton]; rintro q rfl; exact hd.symm) hS hi) h

/-! ## HMAC's `init`, in a frame of `scratch` -/

/-- What a framed call of HMAC's `init` needs of the state before its push:
the states at `inn` and `out` in `r0` and `r1`, the `kl` bytes of key at `k`
in `r2` and `r3`, and `8 Wi` bytes of scratch space at `sc` in `r12`; the
regions the callee may read and write; that they are disjoint as it needs,
and from the 24 bytes below the stack pointer; and that none of them wraps
around. -/
structure HiArgs (S : StreamingHash) (Wi : Nat) (s : State) (inn out k sc : BitVec 32) (kl : Nat) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = out
  r2 : s.gpr .r2 = k
  r3 : s.gpr .r3 = BitVec.ofNat 32 kl
  r12 : s.gpr .r12 = sc
  klB : kl ≤ S.H.blockSize
  kl32 : kl < 2 ^ 32
  sp : 24 ≤ s.sp.toNat
  cr : Covers [⟨State.addr k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr out, S.stateBytes⟩, ⟨State.addr sc, Wi * 8⟩] s.wr
  i_o : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr out, S.stateBytes⟩
  i_k : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr k, kl⟩
  i_s : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr sc, Wi * 8⟩
  o_k : Region.Disjoint ⟨State.addr out, S.stateBytes⟩ ⟨State.addr k, kl⟩
  o_s : Region.Disjoint ⟨State.addr out, S.stateBytes⟩ ⟨State.addr sc, Wi * 8⟩
  k_s : Region.Disjoint ⟨State.addr k, kl⟩ ⟨State.addr sc, Wi * 8⟩
  b_i : (stk s).Disjoint ⟨State.addr inn, S.stateBytes⟩
  b_o : (stk s).Disjoint ⟨State.addr out, S.stateBytes⟩
  b_k : (stk s).Disjoint ⟨State.addr k, kl⟩
  b_s : (stk s).Disjoint ⟨State.addr sc, Wi * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  no : out.toNat + S.stateBytes ≤ 2 ^ 32
  nk : k.toNat + kl ≤ 2 ^ 32
  nsc : sc.toNat + Wi * 8 ≤ 2 ^ 32

/-- The frame of HMAC's `init` and of `iterate`. -/
abbrev fr1 : List Reg := [.r12, .lr]

/-- The regions `init` is given. -/
abbrev HiArgs.rd (sp k : BitVec 32) (kl : Nat) : List Region :=
  [⟨State.addr k, kl⟩, ⟨State.addr (sp - BitVec.ofNat 32 8), 4⟩]
abbrev HiArgs.wr (S : StreamingHash) (Wi : Nat) (inn out sc : BitVec 32) : List Region :=
  [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr out, S.stateBytes⟩, ⟨State.addr sc, Wi * 8⟩]

namespace HiArgs
variable {S : StreamingHash} {Wi : Nat} {s : State} {inn out k sc : BitVec 32} {kl : Nat}
  (h : HiArgs S Wi s inn out k sc kl)
include h

/-- `init`'s precondition on entry. -/
theorem pre : (Spec.Hmac.initContract S Wi Arm.abi 16).pre
    ((pushed fr1 s).callEntry.withRegions (HiArgs.rd s.sp k kl) (HiArgs.wr S Wi inn out sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  have sA := p2_sub (s := s) e
  have sR := p2_csub (s := s) e
  have cA := p2_cdisj (s := s) e (n := 4) (by decide)
  have sA4 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ (stk s) := fun x hx => sA x (Region.sub_prefix (by decide) x hx)
  sig_pre [Spec.Hmac.initContract, Spec.Hmac.initSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [h.r0, h.r1, h.r2, h.r3, p2_arg0 (s := s) (by omega), p2_argAddr, h.r12, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h.kl32]
  exact ⟨by rw [h8]; omega, by rw [h8]; have := s.sp.isLt; omega, rfl, rfl, h.i_o, h.i_k, h.i_s,
    (h.b_i.sub_left sA4).symm, h.o_k, h.o_s, (h.b_o.sub_left sA4).symm, h.k_s, (h.b_s.sub_left sA4).symm,
    h.b_i.sub_left sR, h.b_o.sub_left sR, h.b_k.sub_left sR, h.b_s.sub_left sR, cA,
    h.ni, h.no, h.nk, h.nsc, h.klB⟩

theorem cov : Covers (HiArgs.rd s.sp k kl ++ HiArgs.wr S Wi inn out sc) ((pushed fr1 s).rd ++ (pushed fr1 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ a n
    simp only [Region.Contains] at hc ⊢; omega
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (HiArgs.wr S Wi inn out sc) (pushed fr1 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end HiArgs

theorem hi_frame {S : StreamingHash} {Wi : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (Spec.Hmac.initContract S Wi Arm.abi 16)) (hst : armStack c ≤ 16)
    {s : State} {inn out k sc : BitVec 32} {kl : Nat} (h : HiArgs S Wi s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', After s (HiArgs.wr S Wi inn out sc) s' →
      S.Repr s'.mem (State.addr inn) (xorPad (blockKey S.H (bytesAt s.mem (State.addr k) kl)) ipad) →
      S.Repr s'.mem (State.addr out) (xorPad (blockKey S.H (bytesAt s.mem (State.addr k) kl)) opad) → Q s') :
    WP isa (.frame (.push fr1) (.call n c) (.pop .r12 8)) s Q := by
  refine frame2_ok rfl (by decide) hv.ok hst h.sp h.pre h.cov h.covW fun s₂ a post => ?_
  sig_post [Spec.Hmac.initContract, Spec.Hmac.initSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at post
  simp only [
    h.r0, h.r1, h.r2, h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.kl32] at post
  have ek : bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 k) kl =
      bytesAt s.mem (State.addr k) kl :=
    p2_bytes (ra := .r12) (rb := .lr) h.sp h.b_k (by have := h.kl32; omega)
  rw [ek] at post
  exact hQ _ a (by rw [popped_mem]; exact post.1) (by rw [popped_mem]; exact post.2)

theorem hi_rel {S : StreamingHash} {Wi : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (Spec.Hmac.initContract S Wi Arm.abi 16)) {P : State → State → Prop}
    {sp inn out k sc : BitVec 32} {kl : Nat}
    (h : ∀ s s', P s s' → HiArgs S Wi s inn out k sc kl ∧ HiArgs S Wi s' inn out k sc kl ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push fr1) (.call n c) (.pop .r12 8)) fun _ _ => True := by
  refine frame2_rel rfl hv.ok hv.ct (HiArgs.rd sp k kl) (HiArgs.wr S Wi inn out sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [Spec.Hmac.initContract, Spec.Hmac.initSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [
    a.r0, a'.r0, a.r1, a'.r1, a.r2, a'.r2, a.r3, a'.r3, p2_arg0 (s := s) (by have := a.sp; omega),
    p2_arg0 (s := s') (by have := a'.sp; omega), a.r12, a'.r12, e, e', and_self]

/-! ## HMAC's `finalize`, in a frame of `out` and `scratch` -/

/-- What a framed call of HMAC's `finalize` needs of the state before its
push: the inner and outer states at `inn` and `ou` in `r0` and `r1`, the
count in `r3:r2`, `out` at `o` in `r10` and `8 Wf` bytes of scratch space
at `sc` in `r12`, as for `init`. -/
structure HfArgs (S : StreamingHash) (Wf : Nat) (s : State) (inn ou o sc : BitVec 32) : Prop where
  r0 : s.gpr .r0 = inn
  r1 : s.gpr .r1 = ou
  r10 : s.gpr .r10 = o
  r12 : s.gpr .r12 = sc
  sp : 24 ≤ s.sp.toNat
  cr : Covers [⟨State.addr ou, S.stateBytes⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr o, S.digestBytes⟩, ⟨State.addr sc, Wf * 8⟩] s.wr
  i_u : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr ou, S.stateBytes⟩
  i_o : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr o, S.digestBytes⟩
  i_s : Region.Disjoint ⟨State.addr inn, S.stateBytes⟩ ⟨State.addr sc, Wf * 8⟩
  u_o : Region.Disjoint ⟨State.addr ou, S.stateBytes⟩ ⟨State.addr o, S.digestBytes⟩
  u_s : Region.Disjoint ⟨State.addr ou, S.stateBytes⟩ ⟨State.addr sc, Wf * 8⟩
  o_s : Region.Disjoint ⟨State.addr o, S.digestBytes⟩ ⟨State.addr sc, Wf * 8⟩
  b_i : (stk s).Disjoint ⟨State.addr inn, S.stateBytes⟩
  b_u : (stk s).Disjoint ⟨State.addr ou, S.stateBytes⟩
  b_o : (stk s).Disjoint ⟨State.addr o, S.digestBytes⟩
  b_s : (stk s).Disjoint ⟨State.addr sc, Wf * 8⟩
  ni : inn.toNat + S.stateBytes ≤ 2 ^ 32
  nu : ou.toNat + S.stateBytes ≤ 2 ^ 32
  no : o.toNat + S.digestBytes ≤ 2 ^ 32
  nsc : sc.toNat + Wf * 8 ≤ 2 ^ 32

/-- The frame of HMAC's `finalize`. -/
abbrev fr2 : List Reg := [.r10, .r12]

/-- The regions `finalize` is given. -/
abbrev HfArgs.rd (S : StreamingHash) (sp ou : BitVec 32) : List Region :=
  [⟨State.addr ou, S.stateBytes⟩, ⟨State.addr (sp - BitVec.ofNat 32 8), 8⟩]
abbrev HfArgs.wr (S : StreamingHash) (Wf : Nat) (inn o sc : BitVec 32) : List Region :=
  [⟨State.addr inn, S.stateBytes⟩, ⟨State.addr o, S.digestBytes⟩, ⟨State.addr sc, Wf * 8⟩]

namespace HfArgs
variable {S : StreamingHash} {Wf : Nat} {s : State} {inn ou o sc : BitVec 32}
  (h : HfArgs S Wf s inn ou o sc)
include h

theorem pre : (Spec.Hmac.finalizeContract S Wf Arm.abi 16).pre
    ((pushed fr2 s).callEntry.withRegions (HfArgs.rd S s.sp ou) (HfArgs.wr S Wf inn o sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  have sA := p2_sub (s := s) e
  have sR := p2_csub (s := s) e
  have cA := p2_cdisj (s := s) e (n := 8) (by decide)
  sig_pre [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [h.r0, h.r1, p2_arg0 (s := s) (by omega), p2_arg1, p2_argAddr, h.r10, h.r12]
  exact ⟨by rw [h8]; omega, by rw [h8]; have := s.sp.isLt; omega, rfl, rfl, h.i_u, h.i_o, h.i_s,
    (h.b_i.sub_left sA).symm, h.u_o, h.u_s, h.o_s, (h.b_o.sub_left sA).symm, (h.b_s.sub_left sA).symm,
    h.b_i.sub_left sR, h.b_u.sub_left sR, h.b_o.sub_left sR, h.b_s.sub_left sR, cA,
    h.ni, h.nu, h.no, h.nsc⟩

theorem cov : Covers (HfArgs.rd S s.sp ou ++ HfArgs.wr S Wf inn o sc) ((pushed fr2 s).rd ++ (pushed fr2 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_singleton_self _, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · exact ⟨_, List.mem_append_right _ List.mem_cons_self, hc⟩
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (HfArgs.wr S Wf inn o sc) (pushed fr2 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end HfArgs

theorem hf_frame {S : StreamingHash} {Wf : Nat} {n : String} {c : Prog isa} (hR : ReprOK S)
    (hSn : S.stateBytes ≤ 2 ^ 64) (hv : Sound c (Spec.Hmac.finalizeContract S Wf Arm.abi 16))
    (hst : armStack c ≤ 16) {s : State} {inn ou o sc : BitVec 32} (h : HfArgs S Wf s inn ou o sc)
    {Q : State → Prop}
    (hQ : ∀ s', After s (HfArgs.wr S Wf inn o sc) s' →
      (∀ k0 text, k0.length = S.H.blockSize → k0.length + text.length < 2 ^ 64 →
        S.Repr s.mem (State.addr inn) (xorPad k0 ipad ++ text) →
        s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 (S.H.blockSize + text.length) →
        S.Repr s.mem (State.addr ou) (xorPad k0 opad) →
        bytesAt s'.mem (State.addr o) S.digestBytes = hmacBlockKey S.H k0 text) → Q s') :
    WP isa (.frame (.push fr2) (.call n c) (.pop .r12 8)) s Q := by
  refine frame2_ok rfl (by decide) hv.ok hst h.sp h.pre h.cov h.covW fun s₂ a post => ?_
  sig_post [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at post
  simp only [h.r0, h.r1, p2_arg0 (s := s) (by have := h.sp; omega)] at post
  refine hQ _ a fun k0 text hk hl hi hc ho => ?_
  rw [popped_mem, ← h.r10]
  exact post k0 text hk hl (p2_repr (ra := .r10) (rb := .r12) hR hSn h.sp h.b_i hi) hc
    (p2_repr (ra := .r10) (rb := .r12) hR hSn h.sp h.b_u ho)

theorem hf_rel {S : StreamingHash} {Wf : Nat} {n : String} {c : Prog isa}
    (hv : Sound c (Spec.Hmac.finalizeContract S Wf Arm.abi 16)) {P : State → State → Prop}
    {sp inn ou o sc : BitVec 32}
    (h : ∀ s s', P s s' → HfArgs S Wf s inn ou o sc ∧ HfArgs S Wf s' inn ou o sc ∧
      s.gpr .r2 = s'.gpr .r2 ∧ s.gpr .r3 = s'.gpr .r3 ∧ s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push fr2) (.call n c) (.pop .r12 8)) fun _ _ => True := by
  refine frame2_rel rfl hv.ok hv.ct (HfArgs.rd S sp ou) (HfArgs.wr S Wf inn o sc) fun s s' hp => ?_
  obtain ⟨a, a', c2, c3, e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [
    a.r0, a'.r0, a.r1, a'.r1, c2, c3, p2_arg0 (s := s) (by have := a.sp; omega),
    p2_arg0 (s := s') (by have := a'.sp; omega), p2_arg1,
    p2_arg1 (s := s'), a.r10, a'.r10, a.r12, a'.r12, e, e', and_self]

/-! ## `iterate`, in a frame of `scratch` -/

/-- What a framed call of `iterate` needs of the state before its push: the
key's states at `key` in `r0`, `U` at `u` in `r1`, `n` in `r2`, `T` at `tt`
in `r3` and `8 Wt` bytes of scratch space at `sc` in `r12`, as for `init`. -/
structure ItArgs (S : StreamingHash) (Wt : Nat) (s : State) (key u n tt sc : BitVec 32) : Prop where
  r0 : s.gpr .r0 = key
  r1 : s.gpr .r1 = u
  r2 : s.gpr .r2 = n
  r3 : s.gpr .r3 = tt
  r12 : s.gpr .r12 = sc
  sp : 24 ≤ s.sp.toNat
  cr : Covers [⟨State.addr key, 2 * S.stateBytes⟩, ⟨State.addr u, S.digestBytes⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr tt, S.digestBytes⟩, ⟨State.addr sc, Wt * 8⟩] s.wr
  k_t : Region.Disjoint ⟨State.addr key, 2 * S.stateBytes⟩ ⟨State.addr tt, S.digestBytes⟩
  k_s : Region.Disjoint ⟨State.addr key, 2 * S.stateBytes⟩ ⟨State.addr sc, Wt * 8⟩
  u_t : Region.Disjoint ⟨State.addr u, S.digestBytes⟩ ⟨State.addr tt, S.digestBytes⟩
  u_s : Region.Disjoint ⟨State.addr u, S.digestBytes⟩ ⟨State.addr sc, Wt * 8⟩
  t_s : Region.Disjoint ⟨State.addr tt, S.digestBytes⟩ ⟨State.addr sc, Wt * 8⟩
  b_k : (stk s).Disjoint ⟨State.addr key, 2 * S.stateBytes⟩
  b_u : (stk s).Disjoint ⟨State.addr u, S.digestBytes⟩
  b_t : (stk s).Disjoint ⟨State.addr tt, S.digestBytes⟩
  b_s : (stk s).Disjoint ⟨State.addr sc, Wt * 8⟩
  nk : key.toNat + 2 * S.stateBytes ≤ 2 ^ 32
  nu : u.toNat + S.digestBytes ≤ 2 ^ 32
  nt : tt.toNat + S.digestBytes ≤ 2 ^ 32
  nsc : sc.toNat + Wt * 8 ≤ 2 ^ 32

/-- The regions `iterate` is given. -/
abbrev ItArgs.rd (S : StreamingHash) (sp key u : BitVec 32) : List Region :=
  [⟨State.addr key, 2 * S.stateBytes⟩, ⟨State.addr u, S.digestBytes⟩, ⟨State.addr (sp - BitVec.ofNat 32 8), 4⟩]
abbrev ItArgs.wr (S : StreamingHash) (Wt : Nat) (tt sc : BitVec 32) : List Region :=
  [⟨State.addr tt, S.digestBytes⟩, ⟨State.addr sc, Wt * 8⟩]

namespace ItArgs
variable {S : StreamingHash} {Wt : Nat} {s : State} {key u n tt sc : BitVec 32}
  (h : ItArgs S Wt s key u n tt sc)
include h

theorem pre : (Spec.Pbkdf2.iterateContract S Wt Arm.abi 16).pre
    ((pushed fr1 s).callEntry.withRegions (ItArgs.rd S s.sp key u) (ItArgs.wr S Wt tt sc)) := by
  have e := h.sp
  have h8 : (s.sp - BitVec.ofNat 32 8).toNat = s.sp.toNat - 8 := sub_toNat' (by omega)
  have sA := p2_sub (s := s) e
  have sR := p2_csub (s := s) e
  have cA := p2_cdisj (s := s) e (n := 4) (by decide)
  have sA4 : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ (stk s) := fun x hx => sA x (Region.sub_prefix (by decide) x hx)
  sig_pre [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [h.r0, h.r1, h.r3, p2_arg0 (s := s) (by omega), p2_argAddr, h.r12]
  exact ⟨by rw [h8]; omega, by rw [h8]; have := s.sp.isLt; omega, rfl, rfl, h.k_t, h.k_s, h.u_t, h.u_s,
    h.t_s, (h.b_t.sub_left sA4).symm, (h.b_s.sub_left sA4).symm,
    h.b_k.sub_left sR, h.b_u.sub_left sR, h.b_t.sub_left sR, h.b_s.sub_left sR, cA,
    h.nk, h.nu, h.nt, h.nsc⟩

theorem cov : Covers (ItArgs.rd S s.sp key u ++ ItArgs.wr S Wt tt sc) ((pushed fr1 s).rd ++ (pushed fr1 s).wr) := by
  intro a n ⟨q, hq, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rw [pushed_rd, pushed_wr]
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_cons_self, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · obtain ⟨q', hq', hc'⟩ := h.cr a n ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hc⟩
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact ⟨q', List.mem_append_left _ hq', hc'⟩
    · exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩
  · refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    show Region.Contains ⟨State.addr (s.sp - BitVec.ofNat 32 8), 8⟩ a n
    simp only [Region.Contains] at hc ⊢; omega
  all_goals
    obtain ⟨q', hq', hc'⟩ := h.cw a n ⟨_, by simp, hc⟩
    exact ⟨q', List.mem_append_right _ (List.mem_cons_of_mem _ hq'), hc'⟩

theorem covW : Covers (ItArgs.wr S Wt tt sc) (pushed fr1 s).wr := by
  intro a n hi
  obtain ⟨q', hq', hc'⟩ := h.cw a n hi
  exact ⟨q', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hq', hc'⟩

end ItArgs

theorem it_frame {S : StreamingHash} {Wt : Nat} {nm : String} {c : Prog isa} (hR : ReprOK S)
    (hSn : 2 * S.stateBytes ≤ 2 ^ 32) (hDn : S.digestBytes ≤ 2 ^ 32)
    (hv : Sound c (Spec.Pbkdf2.iterateContract S Wt Arm.abi 16)) (hst : armStack c ≤ 16)
    {s : State} {key u n tt sc : BitVec 32} (h : ItArgs S Wt s key u n tt sc) {Q : State → Prop}
    (hQ : ∀ s', After s (ItArgs.wr S Wt tt sc) s' →
      (∀ k0, k0.length = S.H.blockSize → S.Repr s.mem (State.addr key) (xorPad k0 ipad) →
        S.Repr s.mem (State.addr key + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad) →
        bytesAt s'.mem (State.addr tt) S.digestBytes =
          Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) n.toNat (bytesAt s.mem (State.addr u) S.digestBytes)
            (bytesAt s.mem (State.addr tt) S.digestBytes)) → Q s') :
    WP isa (.frame (.push fr1) (.call nm c) (.pop .r12 8)) s Q := by
  refine frame2_ok rfl (by decide) hv.ok hst h.sp h.pre h.cov h.covW fun s₂ a post => ?_
  sig_post [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at post
  simp only [h.r0, h.r1, h.r2, h.r3] at post
  refine hQ _ a fun k0 hk hi ho => ?_
  rw [popped_mem]
  have := post k0 hk
    (p2_repr (ra := .r12) (rb := .lr) (p := State.addr key) hR (by omega) h.sp
      (h.b_k.sub_right (Region.sub_prefix (by omega))) hi)
    (p2_repr (ra := .r12) (rb := .lr) (p := State.addr key + BitVec.ofNat 64 S.stateBytes) hR (by omega) h.sp
      (h.b_k.sub_right (Offset.sub_base _ (by omega))) ho)
  have eu : bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 u)
      S.digestBytes = bytesAt s.mem (State.addr u) S.digestBytes :=
    p2_bytes (ra := .r12) (rb := .lr) h.sp h.b_u (by omega)
  have et : bytesAt (storeWords s.mem (s.sp - BitVec.ofNat 32 8) [s.gpr .r12, s.gpr .lr]) (BitVec.setWidth 64 tt)
      S.digestBytes = bytesAt s.mem (State.addr tt) S.digestBytes :=
    p2_bytes (ra := .r12) (rb := .lr) h.sp h.b_t (by omega)
  rw [eu, et] at this
  exact this

theorem it_rel {S : StreamingHash} {Wt : Nat} {nm : String} {c : Prog isa}
    (hv : Sound c (Spec.Pbkdf2.iterateContract S Wt Arm.abi 16)) {P : State → State → Prop}
    {sp key u n tt sc : BitVec 32}
    (h : ∀ s s', P s s' → ItArgs S Wt s key u n tt sc ∧ ItArgs S Wt s' key u n tt sc ∧ s.sp = sp ∧ s'.sp = sp) :
    RelCT isa P (.frame (.push fr1) (.call nm c) (.pop .r12 8)) fun _ _ => True := by
  refine frame2_rel rfl hv.ok hv.ct (ItArgs.rd S sp key u) (ItArgs.wr S Wt tt sc) fun s s' hp => ?_
  obtain ⟨a, a', e, e'⟩ := h s s' hp
  have c := a.pre; have c' := a'.pre
  rw [e] at c; rw [e'] at c'
  have v := a.cov; have v' := a'.cov
  rw [e] at v; rw [e'] at v'
  refine ⟨e.trans e'.symm, c, c', ?_, v, a.covW, v', a'.covW⟩
  sig_pub [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [
    a.r0, a'.r0, a.r1, a'.r1, a.r2, a'.r2, a.r3, a'.r3, p2_arg0 (s := s) (by have := a.sp; omega),
    p2_arg0 (s := s') (by have := a'.sp; omega), a.r12, a'.r12, e, e', and_self]

end VG.Proof.Pbkdf2.Whole.Arm
