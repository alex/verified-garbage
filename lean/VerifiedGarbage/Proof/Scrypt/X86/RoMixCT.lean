import VerifiedGarbage.Proof.Scrypt.X86.RoMixFun
import VerifiedGarbage.Proof.Scrypt.X86.BlockMixVerified
import VerifiedGarbage.Proof.Framework.X86.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptROMix on x86 (32-bit): verified

`BlockMixSpec` of the verified `vg_scrypt_blockmix`, from its proof by
`WP.callWith`; then constant time, up to the indices `j`, as on 32-bit ARM
(`Proof/Scrypt/Arm/RoMixCT.lean`): the taint analysis cannot follow the calls
(scryptBlockMix stores secrets through pointers into the middle of `y`, and
restores its caller's registers from memory), so we relate two runs piece by
piece (`RelCT`). Correctness determines our registers from the public
arguments, so they agree between the calls, where the taint analysis proves
each piece constant time, reading the pointers and `r` from the arguments,
which nothing writes; the calls are constant time by scryptBlockMix's own
proof (`RelCT.callWith`). In step 3, the address of `V[j]` depends on `j`,
which the contract declares public: the two runs compute the same `j`, since
both compute their indices in order (`Inv3.js`) and agree on the whole list.
The proof is written against a contract under which the code only reads its
arguments, and moved to the shared contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt.X86.RoMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_addi wp_subi addr_toNat)
open VG.Proof.Scrypt.Memory (InRegions.right frame_bytesAt)

/-! ## The call of `vg_scrypt_blockmix` -/

theorem blockMix_nosp : NoSp Impl.Scrypt.X86.blockMix := NoSp.of_all (by decide +kernel)

theorem blockMix_stack : stackUse Impl.Scrypt.X86.blockMix = 12 := by decide +kernel

/-- The registers the call pushes, as its arguments. -/
abbrev bmRegs : List Reg := [.eax, .ecx, .edx, .ecx, .esi]

/-- The regions the callee may read and write. -/
def bmRd (E src : BitVec 32) (r : Nat) : List Region :=
  [⟨src.setWidth 64, r * 128⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
def bmWr (dst scr : BitVec 32) (r : Nat) : List Region :=
  [⟨dst.setWidth 64, r * 128⟩, ⟨scr.setWidth 64, 128⟩]

section
variable {s : State} {src dst scr : BitVec 32} {r : Nat} (h0 : s.gpr .esi = src)
  (h1 : s.gpr .ecx = BitVec.ofNat 32 r) (h2 : s.gpr .edx = dst) (h3 : s.gpr .eax = scr)
  (hlo : 36 ≤ (s.gpr .esp).toNat)
include h0 h1 h2 h3 hlo

theorem bm_args :
    arg (pushed bmRegs s).callEntry 0 = src ∧ arg (pushed bmRegs s).callEntry 1 = BitVec.ofNat 32 r ∧
    arg (pushed bmRegs s).callEntry 2 = dst ∧ arg (pushed bmRegs s).callEntry 3 = BitVec.ofNat 32 r ∧
    arg (pushed bmRegs s).callEntry 4 = scr := by
  have hrs : Reg.esp ∉ bmRegs := by decide
  have fit : 4 * bmRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit hrs (by simp)] <;> simp [h0, h1, h2, h3]

/-- The callee's precondition, and the permissions it is given. -/
theorem bm_callPre (hr : 0 < r) (hlt : 128 * r < 2 ^ 32)
    (hds : Region.Disjoint ⟨dst.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩)
    (hsd : Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨dst.setWidth 64, 128 * r⟩)
    (hss : Region.Disjoint ⟨src.setWidth 64, 128 * r⟩ ⟨scr.setWidth 64, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 32) (ndst : dst.toNat + 128 * r ≤ 2 ^ 32)
    (nscr : scr.toNat + 128 ≤ 2 ^ 32)
    (dsrc : (below (s.gpr .esp) 36).Disjoint ⟨src.setWidth 64, 128 * r⟩)
    (ddst : (below (s.gpr .esp) 36).Disjoint ⟨dst.setWidth 64, 128 * r⟩)
    (dscr : (below (s.gpr .esp) 36).Disjoint ⟨scr.setWidth 64, 128⟩)
    (isrc : InRegions (s.rd ++ s.wr) (src.setWidth 64) (128 * r))
    (idst : InRegions s.wr (dst.setWidth 64) (128 * r)) (iscr : InRegions s.wr (scr.setWidth 64) 128) :
    CallPre Proof.Scrypt.blockMixX86 bmRegs (bmRd (s.gpr .esp) src r) (bmWr dst scr r) s := by
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  obtain ⟨a0, a1, a2, a3, a4⟩ := bm_args h0 h1 h2 h3 hlo
  have eA : argAddr (pushed bmRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed bmRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  have b20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 36) := below_sub (by omega) hlo
  have r4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 36) := by
    have := below_inner (sp := s.gpr .esp) (a := 4) (b := 36) (k := 20) (by omega) hlo
    rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      bv_omega]
    exact this
  have s12 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 - 12, 12⟩ (below (s.gpr .esp) 36) := by
    intro a ha
    simp only [Region.Contains] at ha ⊢
    rw [Taint.sub_setWidth (by omega)] at ha ⊢
    have := (s.gpr .esp).isLt
    have hE : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := addr_toNat _
    generalize (s.gpr .esp).setWidth 64 = b at *
    bv_omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Scrypt.blockMixX86, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_gpr, arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eSp, tr,
      bmRd, bmWr, eA]
    rw [c128] at *
    refine ⟨trivial, trivial, hds, hsd, hss, ddst.sub_left b20, dscr.sub_left b20, ddst.sub_left r4,
      dscr.sub_left r4, dsrc.sub_left s12, ddst.sub_left s12, dscr.sub_left s12, nsrc, ndst, nscr,
      ?_, ?_, trivial, hr⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨R, hR, hcn⟩
    simp only [bmRd, bmWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hR
    rw [c128] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · obtain ⟨R', hR', hc'⟩ := isrc
      refine InRegions_append_cons.mpr (.inr ⟨R', hR', ?_⟩)
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · exact InRegions_append_cons.mpr (.inl hcn)
    · obtain ⟨R', hR', hc'⟩ := idst
      refine InRegions_append_cons.mpr (.inr ⟨R', List.mem_append_right _ hR', ?_⟩)
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · obtain ⟨R', hR', hc'⟩ := iscr
      refine InRegions_append_cons.mpr (.inr ⟨R', List.mem_append_right _ hR', ?_⟩)
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
  · intro a n ⟨R, hR, hcn⟩
    simp only [bmWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rw [c128] at hR
    rcases hR with rfl | rfl
    · obtain ⟨R', hR', hc'⟩ := idst
      refine ⟨R', List.mem_cons_of_mem _ hR', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · obtain ⟨R', hR', hc'⟩ := iscr
      refine ⟨R', List.mem_cons_of_mem _ hR', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega

end

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.X86.blockMix := by
  intro s src dst scr r h0 h1 h2 h3 hr hlt hds hsd hss nsrc ndst nscr hlo dsrc ddst dscr isrc idst iscr
    Q hQ
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  have hrs : Reg.esp ∉ bmRegs := by decide
  have fit : 4 * bmRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨a0, a1, a2, -, -⟩ := bm_args h0 h1 h2 h3 hlo
  have e36 : 4 * bmRegs.length + stackUse Impl.Scrypt.X86.blockMix + 4 = 36 := by
    rw [blockMix_stack]; rfl
  refine WP.callWith (k := Proof.Scrypt.blockMixX86) BlockMix.blockMix_correct blockMix_nosp (by simp) hrs
    (by rw [e36]; exact hlo)
    (bm_callPre h0 h1 h2 h3 hlo hr hlt hds hsd hss nsrc ndst nscr dsrc ddst dscr isrc idst iscr)
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  rw [e36] at f'
  have hsE := callEntry_frame fit hrs
  rw [show 4 * bmRegs.length + 4 = 24 from rfl] at hsE
  simp only [Proof.Scrypt.blockMixX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂, tr]
    at post
  refine hQ s' rd' wr' cs' (f'.mono fun R hR => by simpa [bmWr, c128] using hR) ?_
  rw [post]
  congr 1
  refine frame_bytesAt hsE (fun R hR => ?_) (by omega)
  simp only [List.mem_singleton] at hR; subst hR
  exact (dsrc.sub_left (below_sub (by omega) hlo)).symm

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 6, arg s₀ i = arg s₀' i

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.esp₀ : esp₀ s₀ = esp₀ s₀' := hq.esp
theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.args 1 (by omega)]
theorem PubEq.NN : NN s₀ = NN s₀' := by
  simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.args 1 (by omega), hq.args 3 (by omega)]
theorem PubEq.vAt32 (i : Nat) : vAt32 s₀ i = vAt32 s₀' i := by
  simp only [RoMix.vAt32, RoMix.vP, RoMix.rr, hq.args 1 (by omega), hq.args 2 (by omega)]
theorem PubEq.tP32 : tP32 s₀ = tP32 s₀' := by simp only [RoMix.tP32, RoMix.sc, hq.args 4 (by omega)]

end

/-- The taint state in which the registers `rs` and the arguments are public. -/
def τk (rs : List Reg) : VG.X86.Taint.T := { regs := .ofList rs, flags := false, argLen := 28 }

theorem wf_k {s₀ : State} (hp : Pre s₀) (rs : List Reg) {s : State} (h : Base s₀ s) :
    VG.X86.Taint.Wf (τk rs) s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by rw [h.esp]; exact hs, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [h.wr, hp.wr, h.esp, τk, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_b hp.a_b
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_v hp.a_v
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_s hp.a_s

theorem Base.argW {s₀ : State} (hp : Pre s₀) {s : State} (h : Base s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (argAddr s i) 32 = VG.X86.arg s₀ i :=
  h.arg hp hi

/-- Two runs agree on `esp`, the arguments and the registers `rs`. -/
theorem agree_k {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀') {rs : List Reg}
    {s s' : State} (h : Base s₀ s) (h' : Base s₀' s') (hr : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    VG.X86.Taint.Agree (τk (.esp :: rs)) s s' := by
  have f₁ : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := by rw [h.esp]; exact hp.sp_fit
  have f₂ : (s'.gpr .esp).toNat + 28 ≤ 2 ^ 32 := by rw [h'.esp]; exact hp'.sp_fit
  refine ⟨⟨fun r hr' => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf_k hp _ h, wf_k hp' _ h',
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => by rw [h.esp, h'.esp, hq.esp₀], fun k h4 hk => ?_⟩
  · simp only [τk, RegSet.mem_ofList, List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · rw [h.esp, h'.esp, hq.esp₀]
    · exact hr r hr'
  · simp only [τk] at hk
    rw [show VG.X86.Taint.depth (τk (.esp :: rs)).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s'.mem _ (Nat.mod_lt _ (by omega)),
      h.argW hp (i := (k - 4) / 4) (by omega), h'.argW hp' (i := (k - 4) / 4) (by omega),
      hq.args _ (by omega)]

/-- The registers the pieces of an iteration keep: `ebx = q` and `ebp = N`. -/
structure KR (s₀ : State) (q : BitVec 32) (s : State) : Prop extends Base s₀ s where
  ebx : s.gpr .ebx = q
  ebp : s.gpr .ebp = BitVec.ofNat 32 (NN s₀)

/-- Whether an instruction writes none of `rs`. -/
def free (rs : List Reg) (i : Instr) : Bool := rs.all fun r => !Taint.clobbers i r

/-- Registers that code writing none of them keeps. -/
theorem exec_keeps {c : Prog isa} {rs : List Reg} (hc : c.allInstrs (free rs) = true) {s s' : State}
    {t : List Leak} (he : Exec isa c s t s') : ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  intro r hr
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine Exec.gpr (fun i hi => ?_) he
  have := hc i (instrs_eq_instrs c ▸ hi)
  simp only [free, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this r hr

/-- `Base` survives code without calls that never writes `esp`. -/
theorem Base.exec {c : Prog isa} (hc : c.allInstrs (free [.esp]) = true) (hn : c.noCalls = true)
    {s₀ : State} (hp : Pre s₀) {s s' : State} {t : List Leak} (he : Exec isa c s t s') (h : Base s₀ s) :
    Base s₀ s' := by
  obtain ⟨rd, wr, f⟩ := Exec.regions he hn
  refine ⟨rd.trans h.rd, wr.trans h.wr, by rw [exec_keeps hc he _ (by simp), h.esp],
    h.frame.trans (f.mono ?_)⟩
  rw [h.wr, hp.wr]; simp

/-- `KR` survives code without calls that writes none of `esp`, `ebx` and `ebp`. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs (free [.esp, .ebx, .ebp]) = true)
    (hn : c.noCalls = true) {s₀ : State} (hp : Pre s₀) {q : BitVec 32} {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (h : KR s₀ q s) : KR s₀ q s' := by
  have k := exec_keeps hc he
  obtain ⟨rd, wr, f⟩ := Exec.regions he hn
  exact ⟨⟨rd.trans h.rd, wr.trans h.wr, by rw [k _ (by simp), h.esp],
    h.frame.trans (f.mono (by rw [h.wr, hp.wr]; simp))⟩, by rw [k _ (by simp), h.ebx],
    by rw [k _ (by simp), h.ebp]⟩

/-- A relation that each run keeps, from what its own run does. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True)
    (hk : ∀ s s' t t' u u', P s s' → Exec isa c s t u → Exec isa c s' t' u' → F₁ u ∧ F₂ u') :
    RelCT isa P c fun u u' => F₁ u ∧ F₂ u' :=
  fun _ _ _ _ _ _ hp e e' => ⟨(h _ _ _ _ _ _ hp e e').1, hk _ _ _ _ _ _ hp e e'⟩

theorem RelCT.assoc {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ bc₁ =>
    cases bc₁ with
    | seq b₁ c₁ =>
      cases e₂ with
      | seq a₂ bc₂ =>
        cases bc₂ with
        | seq b₂ c₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ b₁) c₁) (.seq (.seq a₂ b₂) c₂)
          simp only [List.append_assoc] at ht
          exact ⟨ht, hq⟩

theorem eval_zf {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map (!·) = _; rw [h]; rfl

/-! ## The call of `vg_scrypt_blockmix`, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem call_rel {A A' : BitVec 32} (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A')
    {q q' : BitVec 32} :
    RelCT isa (fun s s' => (KR s₀ q s ∧ s.gpr .esi = A) ∧ (KR s₀' q' s' ∧ s'.gpr .esi = A'))
      (blockMixTo Impl.Scrypt.X86.blockMix)
      fun s s' => (KR s₀ q s ∧ s.gpr .esi = A) ∧ (KR s₀' q' s' ∧ s'.gpr .esi = A') := by
  subst hAA
  have lt := r_lt hp
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have eb : bP s₀' = bP s₀ := (hq.args 0 (by omega)).symm
  have es : sc s₀' = sc s₀ := (hq.args 4 (by omega)).symm
  -- The arguments, set in each run.
  let F (t₀ : State) (q : BitVec 32) (s : State) : Prop :=
    KR t₀ q s ∧ s.gpr .esi = A ∧ s.gpr .eax = sc t₀ ∧ s.gpr .ecx = BitVec.ofNat 32 (rr t₀) ∧
      s.gpr .edx = bP t₀
  have wpArgs : ∀ {t₀ : State} {q : BitVec 32}, Pre t₀ → ∀ s, KR t₀ q s ∧ s.gpr .esi = A →
      WP isa (.block bmArgs) s (F t₀ q) := fun hp s h =>
    bmArgs_ok hp h.1.toBase fun s' b' m' k' hax hcx hdx =>
      ⟨⟨b', by rw [k' _ (by decide) (by decide) (by decide), h.1.ebx],
        by rw [k' _ (by decide) (by decide) (by decide), h.1.ebp]⟩,
        by rw [k' _ (by decide) (by decide) (by decide), h.2], hax, hcx, hdx⟩
  have ar : RelCT isa (fun s s' => (KR s₀ q s ∧ s.gpr .esi = A) ∧ (KR s₀' q' s' ∧ s'.gpr .esi = A))
      (.block bmArgs) fun s s' => F s₀ q s ∧ F s₀' q' s' :=
    RelCT.mono ((RelCT.taint (A := taint) (τk [.esp]) (fun _ _ h => agree_k hp hp' hq (rs := [])
      h.1.1.toBase h.2.1.toBase (by simp)) (by taint_decide)).wp
      fun s s' h => ⟨wpArgs hp s h.1, wpArgs hp' s' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2
  -- The call, from each run's `F`.
  have wpCall : ∀ {t₀ : State} {q : BitVec 32}, Pre t₀ → SrcOK t₀ A → ∀ s, F t₀ q s →
      WP isa (.frame (.push bmRegs) (.call "vg_scrypt_blockmix" Impl.Scrypt.X86.blockMix) (.pop .eax 5))
        s (fun s' => KR t₀ q s' ∧ s'.gpr .esi = A) := fun hp hA s h =>
    bmFrame_ok blockMixSpec hp hA h.1.toBase h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      fun s' hrd hwr hcs hf _ => ⟨⟨⟨by rw [hrd, h.1.rd], by rw [hwr, h.1.wr],
        by rw [hcs _ (by simp [calleeSaved]), h.1.esp], h.1.frame.trans (call_frame hf)⟩,
        by rw [hcs _ (by simp [calleeSaved]), h.1.ebx], by rw [hcs _ (by simp [calleeSaved]), h.1.ebp]⟩,
        by rw [hcs _ (by simp [calleeSaved]), h.2.1]⟩
  have cl : RelCT isa (fun s s' => F s₀ q s ∧ F s₀' q' s')
      (.frame (.push bmRegs) (.call "vg_scrypt_blockmix" Impl.Scrypt.X86.blockMix) (.pop .eax 5))
      fun s s' => (KR s₀ q s ∧ s.gpr .esi = A) ∧ (KR s₀' q' s' ∧ s'.gpr .esi = A) := by
    refine RelCT.mono ((RelCT.callWith (k := Proof.Scrypt.blockMixX86) BlockMix.blockMix_correct
      BlockMix.blockMix_ct (bmRd (esp₀ s₀) A (rr s₀)) (bmWr (bP s₀) (sc s₀) (rr s₀))
      fun s s' ⟨h, h'⟩ => ?_).wp fun s s' h => ⟨wpCall hp hA s h.1, wpCall hp' hA' s' h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2
    have pre : ∀ {t₀ : State} {q : BitVec 32} {s : State}, Pre t₀ → SrcOK t₀ A → F t₀ q s →
        CallPre Proof.Scrypt.blockMixX86 bmRegs (bmRd (esp₀ t₀) A (rr t₀)) (bmWr (bP t₀) (sc t₀) (rr t₀)) s := by
        intro t₀ _ s hp hA h
        have hsub : Region.Sub ⟨scA t₀, 128⟩ (scR t₀) := w_sub
        have := bm_callPre h.2.1 h.2.2.2.1 h.2.2.2.2 h.2.2.1 (by rw [h.1.esp]; exact hp.sp_lo) hp.pos
          (r_lt hp) ((hp.b_s.sub_left b_sub').sub_right hsub) hA.b hA.w hA.nw
          (by have := hp.b_nw; omega) (by have := hp.s_nw; omega) (by rw [h.1.esp]; exact hA.stk)
          (by rw [h.1.esp]; exact hp.stk_b.sub_right b_sub') (by rw [h.1.esp]; exact hp.stk_s.sub_right hsub)
          (by rw [h.1.rd, h.1.wr]; exact hA.inr) (by rw [h.1.wr]; exact b_in hp)
          (by rw [h.1.wr]; exact w_in hp)
        rwa [h.1.esp] at this
    have p₁ := pre hp hA h
    have p₂ := pre hp' hA' h'
    rw [show esp₀ s₀' = esp₀ s₀ from hq.esp₀.symm, er, eb, es] at p₂
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.1.esp, h'.1.esp, hq.esp₀]
    have fit : 4 * bmRegs.length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.1.esp]; have := hp.sp_lo; simp only [List.length_cons, List.length_nil]; omega
    refine ⟨p₁, p₂, hsp, ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp], fun i hi => ?_⟩⟩
    simp only [arg_withRegions]
    have hi' : i < bmRegs.length := by simp only [List.length_cons, List.length_nil]; omega
    refine callEntry_arg_eq (by decide) fit hsp (fun r hr => ?_) hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [h.2.2.1, h'.2.2.1, es]
    · rw [h.2.2.2.1, h'.2.2.2.1, er]
    · rw [h.2.2.2.2, h'.2.2.2.2, eb]
    · rw [h.2.2.2.1, h'.2.2.2.1, er]
    · rw [h.2.1, h'.2.1]
  exact ar.seq cl

end

/-- `KR` and `esi` survive code without calls that writes none of `esp`,
`ebx`, `ebp` and `esi`. -/
theorem KR.exec' {c : Prog isa} (hc : c.allInstrs (free [.esp, .ebx, .ebp, .esi]) = true)
    (hn : c.noCalls = true) {s₀ : State} (hp : Pre s₀) {q x : BitVec 32} {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (h : KR s₀ q s ∧ s.gpr .esi = x) : KR s₀ q s' ∧ s'.gpr .esi = x := by
  have k := exec_keeps hc he
  obtain ⟨rd, wr, f⟩ := Exec.regions he hn
  exact ⟨⟨⟨rd.trans h.1.rd, wr.trans h.1.wr, by rw [k _ (by simp), h.1.esp],
    h.1.frame.trans (f.mono (by rw [h.1.wr, hp.wr]; simp))⟩, by rw [k _ (by simp), h.1.ebx],
    by rw [k _ (by simp), h.1.ebp]⟩, by rw [k _ (by simp), h.2]⟩

/-- `tBlock`: `esi = T`. -/
theorem t_wp {s₀ : State} (hp : Pre s₀) {q : BitVec 32} {s : State} (h : KR s₀ q s) :
    WP isa (.block tBlock) s fun s' => KR s₀ q s' ∧ s'.gpr .esi = tP32 s₀ := by
  unfold tBlock
  refine wp_arg (i := 4) hp h.toBase (by omega) fun a ua => wp_addi fun b ub => WP.block_nil ?_
  exact ⟨⟨(h.toBase.upd ua (by decide)).upd ub (by decide),
    by rw [ub.other _ (by decide), ua.other _ (by decide), h.ebx],
    by rw [ub.other _ (by decide), ua.other _ (by decide), h.ebp]⟩, by rw [ub.gpr, ua.gpr]; rfl⟩

/-! ## Step 2, in two runs -/

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.X86.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv2 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt32 s₀ i = vAt32 s₀' i := hq.vAt32 i
  have eq : BitVec.ofNat 32 (NN s₀ - i) = BitVec.ofNat 32 (NN s₀' - i) := by rw [hq.NN]
  have en : BitVec.ofNat 32 (NN s₀) = BitVec.ofNat 32 (NN s₀') := by rw [hq.NN]
  let K (t₀ t : State) : Prop := KR t₀ (BitVec.ofNat 32 (NN t₀ - i)) t ∧ t.gpr .esi = vAt32 t₀ i
  have regs : ∀ {s s'}, K s₀ s → K s₀' s' → ∀ r ∈ [Reg.ebx, .esi, .ebp], s.gpr r = s'.gpr r := by
    intro s s' h h' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.1.ebx, h'.1.ebx, eq]
    · rw [h.2, h'.2, ev]
    · rw [h.1.ebp, h'.1.ebp, en]
  have Kof : ∀ {t₀ t : State}, Inv2 t₀ i t → K t₀ t := fun h => ⟨⟨h.toBase, h.ebx, h.ebp⟩, h.esi⟩
  have ac : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.seq (.block (timesR 32 ++ ([.mov .edx (.reg .eax), .mov .eax (.mem (at_ .esp 4)),
        .mov .ecx (.reg .esi)] : List Instr))) copyLoop) fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.post (RelCT.taint (A := taint) (τk [.esp, .ebx, .esi, .ebp])
      (fun _ _ h => agree_k hp hp' hq h.1.toBase h.2.toBase (regs (Kof h.1) (Kof h.2)))
      (by taint_decide))
      fun _ _ _ _ _ _ h e e' => ⟨KR.exec' (by decide +kernel) (by decide +kernel) hp e (Kof h.1),
        KR.exec' (by decide +kernel) (by decide +kernel) hp' e' (Kof h.2)⟩
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (q := BitVec.ofNat 32 (NN s₀ - i)) (q' := BitVec.ofNat 32 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block (timesR 128 ++ ([.alu .add .esi (.reg .eax), .alu .sub .ebx (.imm 1)] : List Instr)))
      fun _ _ => True :=
    RelCT.taint (A := taint) (τk [.esp, .ebx, .esi, .ebp])
      (fun _ _ h => agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (regs h.1 h.2)) (by taint_decide)
  have body := RelCT.assoc (ac.seq (cl.seq e))
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s')
      (.loop (step2 Impl.Scrypt.X86.blockMix) .ne)
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.X86.blockMix)
    (c := .ne) (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_zf z, eval_zf z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3, in two runs -/

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < NN s₀) {s : State} (h : Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀)).drop i = jOf s₀ s.mem :: rest := by
  have e : NN s₀ - i = NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < NN s₀) (j : Nat) :
    RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧ (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.X86.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have eq : BitVec.ofNat 32 (NN s₀ - i) = BitVec.ofNat 32 (NN s₀' - i) := by rw [hq.NN]
  have en : BitVec.ofNat 32 (NN s₀) = BitVec.ofNat 32 (NN s₀') := by rw [hq.NN]
  have er : BitVec.ofNat 32 (rr s₀ * 128) = BitVec.ofNat 32 (rr s₀' * 128) := by rw [hq.rr]
  let K (t₀ t : State) : Prop := KR t₀ (BitVec.ofNat 32 (NN t₀ - i)) t
  have regs : ∀ {s s'}, K s₀ s → K s₀' s' → ∀ r ∈ [Reg.ebx, .ebp], s.gpr r = s'.gpr r := by
    intro s s' h h' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.ebx, h'.ebx, eq]
    · rw [h.ebp, h'.ebp, en]
  let J (t₀ t : State) : Prop :=
    K t₀ t ∧ t.gpr .eax = BitVec.ofNat 32 j ∧ t.gpr .edi = BitVec.ofNat 32 (rr t₀ * 128)
  have Kof : ∀ {t₀ t : State}, Inv3 t₀ i t → K t₀ t := fun h => ⟨h.toBase, h.ebx, h.ebp⟩
  have jwp : ∀ {t₀ t : State}, Pre t₀ → Inv3 t₀ i t ∧ jOf t₀ t.mem = j →
      WP isa (.block jBlock) t (J t₀) := fun hp h =>
    WP.mono (j_ok hp h.1.toBase h.1.ebp) fun _ ⟨ax, di, o, b, _⟩ =>
      ⟨⟨b, by rw [o _ (by decide) (by decide) (by decide) (by decide), h.1.ebx],
        by rw [o _ (by decide) (by decide) (by decide) (by decide), h.1.ebp]⟩, by rw [ax, h.2], di⟩
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' => J s₀ s ∧ J s₀' s' :=
    RelCT.mono ((RelCT.taint (A := taint) (τk [.esp, .ebx, .ebp])
      (fun _ _ h => agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (regs (Kof h.1.1) (Kof h.2.1)))
      (by taint_decide)).wp fun _ _ h => ⟨jwp hp h.1, jwp hp' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => J s₀ s ∧ J s₀' s') (.seq (.block vjBlock) xorLoop)
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.post (RelCT.taint (A := taint) (τk [.esp, .eax, .edi, .ebx, .ebp])
      (fun _ _ h => agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.1.2.1, h.2.2.1]
        · rw [h.1.2.2, h.2.2.2, er]
        · exact regs h.1.1 h.2.1 _ (by simp)
        · exact regs h.1.1 h.2.1 _ (by simp)))
      (by taint_decide))
      fun _ _ _ _ _ _ h e e' => ⟨KR.exec (by decide +kernel) (by decide +kernel) hp e h.1.1,
        KR.exec (by decide +kernel) (by decide +kernel) hp' e' h.2.1⟩
  have tb : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block tBlock)
      fun s s' => (K s₀ s ∧ s.gpr .esi = tP32 s₀) ∧ (K s₀' s' ∧ s'.gpr .esi = tP32 s₀') :=
    RelCT.mono ((RelCT.taint (A := taint) (τk [.esp, .ebx, .ebp])
      (fun _ _ h => agree_k hp hp' hq h.1.toBase h.2.toBase (regs h.1 h.2)) (by taint_decide)).wp
      fun _ _ h => ⟨t_wp hp h.1, t_wp hp' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP32
    (q := BitVec.ofNat 32 (NN s₀ - i)) (q' := BitVec.ofNat 32 (NN s₀' - i))
  have e : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .esi = tP32 s₀) ∧ (K s₀' s' ∧ s'.gpr .esi = tP32 s₀'))
      (.block [.alu .sub .ebx (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (τk [.esp, .ebx, .ebp])
      (fun _ _ h => agree_k hp hp' hq h.1.1.toBase h.2.1.toBase (regs h.1.1 h.2.1)) (by taint_decide)
  have body := jb.seq (RelCT.assoc (mx.seq (tb.seq (cl.seq e))))
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.X86.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = NN s₀))) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = NN s₀'))) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists_ fun (j : Nat) => body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s')
      (.loop (step3 Impl.Scrypt.X86.blockMix) .ne)
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.X86.blockMix)
    (c := .ne) (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_zf z, eval_zf z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.X86.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.X86.blockMix) _
  unfold roMixWith
  have b₀ : Base s₀ s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  have b₀' : Base s₀' s₀' := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) (τk [.esp]) (P := fun s s' => s = s₀ ∧ s' = s₀')
      (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact agree_k hp hp' hq (rs := []) b₀ b₀' (by simp))
      (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (τk [.esp, .eax, .ecx, .edx])
      (fun _ _ ⟨h, h'⟩ => agree_k hp hp' hq h.toBase h'.toBase fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.eax, h'.eax, hq.rr]
        · rw [h.ecx, h'.ecx]
        · rw [h.edx, h'.edx, RoMix.vl, RoMix.vl, hq.args 3 (by omega)]) (c := nLoop)
      (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (τk [.esp, .ecx])
      (fun _ _ ⟨h, h'⟩ => agree_k hp hp' hq h.toBase h'.toBase fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.ecx, h'.ecx, hq.NN]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (τk [.esp, .ebp])
      (fun _ _ ⟨h, h'⟩ => agree_k hp hp' hq h.toBase h'.toBase fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.ebp, h'.ebp, hq.NN]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok h.1, mid_ok h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τk [.esp])
      (fun _ _ h => agree_k hp hp' hq (rs := []) h.1.toBase h.2.toBase (by simp)) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixX86.pub s₁ s₂) : PubEq s₁ s₂ := ⟨h.1, h.2.1⟩

theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.roMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixX86.post s s' :=
  correct blockMixSpec (pre_of hs)

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixX86.pre Proof.Scrypt.roMixX86.pub
    Impl.Scrypt.X86.roMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x3000, 3` at `0x5004`: `b` at
`0x1000`, `v` at `0x2000` (`N = 1`) and the scratch space at `0x3000` (384 bytes). -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500d then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5015 then 0x30 else if a = 0x5018 then 3 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x5004, 24⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem sat_pre : Proof.Scrypt.roMixX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 1 := by decide
  have a2 : arg sat 2 = 0x2000 := by decide
  have a3 : arg sat 3 = 1 := by decide
  have a4 : arg sat 4 = 0x3000 := by decide
  have a5 : arg sat 5 = 3 := by decide
  have e : argAddr sat 0 = 0x5004 := by decide
  simp only [Proof.Scrypt.roMixX86, a0, a1, a2, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ⟨0, rfl⟩, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

/-! ## The shared contract -/

/-- `roMixX86` with its arguments writable, as the shared contract lets them be. -/
def roMixWide : Contract isa :=
  { Proof.Scrypt.roMixX86 with
    pre := fun s =>
      let r := (arg s 1).toNat
      let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
      let v : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat * 128⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 36, 36⟩
      s.rd = [] ∧ s.wr = [b, v, scratch, args] ∧
      b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
      args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
      ret.Disjoint b ∧ ret.Disjoint v ∧ ret.Disjoint scratch ∧
      stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + (arg s 5).toNat * 128 ≤ 2 ^ 32 ∧ 36 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      0 < r ∧ (arg s 3).toNat % r = 0 ∧ ((arg s 3).toNat / r).isPowerOfTwo ∧ (arg s 5).toNat = r + 2 }

/-- The regions `roMixX86` lets the code read and write. -/
def narrowRd (s : State) : List Region := [⟨argAddr s 0, 24⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat * 128⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩,
    ⟨(arg s 4).setWidth 64, (arg s 5).toNat * 128⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Scrypt.roMixX86, VG.Proof.Scrypt.X86.RoMix.roMixWide,
    VG.Proof.Scrypt.X86.RoMix.narrowRd, VG.Proof.Scrypt.X86.RoMix.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem roMixWide_pre (s : State) (h : roMixWide.pre s) :
    Proof.Scrypt.roMixX86.pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀,
    h₂₁, h₂₂, h₂₃⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉,
    h₂₀, h₂₁, h₂₂, h₂₃⟩

/-- A state satisfying `roMixWide.pre`. -/
def wideSat : State :=
  { sat with rd := [], wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩, ⟨0x5004, 24⟩] }

theorem roMixWide_implies : roMixWide.Implies (Spec.Scrypt.roMixContract X86.abi 36) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 1 := by decide
  have a2 : arg wideSat 2 = 0x2000 := by decide
  have a3 : arg wideSat 3 = 1 := by decide
  have a4 : arg wideSat 4 = 0x3000 := by decide
  have a5 : arg wideSat 5 = 3 := by decide
  have e : argAddr wideSat 0 = 0x5004 := by decide
  have esp : wideSat.gpr .esp = 0x5000 := rfl
  sig_implies [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig, roMixWide,
    Proof.Scrypt.roMixX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using wideSat

/-- The proof is written against `roMixX86`, widened to writable arguments. -/
theorem roMix_verified :
    Verified X86.target Impl.Scrypt.X86.roMix (Spec.Scrypt.roMixContract X86.abi 36) :=
  have hsat := roMixWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct roMix_correct roMix_ct (.refl ⟨sat, sat_pre⟩))
    narrowRd narrowWr roMixWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies roMixWide_implies

end VG.Proof.Scrypt.X86.RoMix
