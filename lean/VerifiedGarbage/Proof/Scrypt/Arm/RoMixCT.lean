import VerifiedGarbage.Proof.Scrypt.Arm.RoMixFun
import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified

/-!
# scryptROMix on 32-bit ARM: verified

Untrusted: everything here is checked by Lean. `BlockMixSpec` of the
verified `vg_scrypt_blockmix`, from its `Verified` proof by `WP.callCalls`;
then constant time, up to the indices `j`, as on AArch64
(`Proof/Scrypt/AArch64/RoMixCT.lean`): we relate two runs (`RelCT`).
Correctness determines our registers from the public arguments, so they
agree between the calls, where the taint analysis proves each piece constant
time; the calls are constant time by scryptBlockMix's own proof. In step 3,
the address of `V[j]` depends on `j`, which the contract declares public: the
two runs compute the same `j`, since both compute their indices in order
(`Inv3.js`) and agree on the whole list.
-/

namespace VG.Proof.Scrypt.Arm.RoMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.Sha256.Arm.Stream (Upd wp_mov wp_add op2_reg op2_imm op2_lsr eval_ne)
open VG.Proof.Scrypt.Arm.BlockMix (covers_of_in)
open VG.Proof.Scrypt.X86_64.BlockMix (InRegions.right)

/-! ## The call of `vg_scrypt_blockmix` -/

theorem covers_of_all {rs rs' : List Region} (h : ∀ R ∈ rs, Covers [R] rs') : Covers rs rs' :=
  fun x n ⟨r, hr, hc⟩ => h r hr x n ⟨_, List.mem_singleton_self _, hc⟩

theorem stackArg_entry (s : State) (rd wr : List Region) :
    stackArg (s.callEntry.withRegions rd wr) 0 = stackArg s 0 := rfl

theorem stackArgAddr_entry (s : State) (rd wr : List Region) :
    stackArgAddr (s.callEntry.withRegions rd wr) 0 = stackArgAddr s 0 := rfl

theorem bm_pre {s : State} {src dst scr : BitVec 32} {r : Nat} (h0 : s.gpr .r0 = src)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 r) (h2 : s.gpr .r2 = dst) (h3 : s.gpr .r3 = BitVec.ofNat 32 r)
    (h4 : stackArg s 0 = scr) (hr : 0 < r) (hlt : 128 * r < 2 ^ 32)
    (hds : Region.Disjoint ⟨State.addr dst, 128 * r⟩ ⟨State.addr scr, 128⟩)
    (hsd : Region.Disjoint ⟨State.addr src, 128 * r⟩ ⟨State.addr dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨State.addr src, 128 * r⟩ ⟨State.addr scr, 128⟩)
    (had : Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr dst, 128 * r⟩)
    (has : Region.Disjoint ⟨stackArgAddr s 0, 4⟩ ⟨State.addr scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 32) (ndst : dst.toNat + 128 * r ≤ 2 ^ 32)
    (nscr : scr.toNat + 128 ≤ 2 ^ 32) (nsp : s.sp.toNat + 4 ≤ 2 ^ 32)
    (isrc : InRegions (s.rd ++ s.wr) (State.addr src) (128 * r))
    (iarg : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4)
    (idst : InRegions s.wr (State.addr dst) (128 * r)) (iscr : InRegions s.wr (State.addr scr) 128) :
    Proof.Scrypt.blockMixArm.pre (s.callEntry.withRegions
      [⟨State.addr src, 128 * r⟩, ⟨stackArgAddr s 0, 4⟩]
      [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩]) ∧
    Covers ([⟨State.addr src, 128 * r⟩, ⟨stackArgAddr s 0, 4⟩] ++
      [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨State.addr dst, 128 * r⟩, ⟨State.addr scr, 128⟩] s.wr := by
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  refine ⟨?_, covers_of_all fun R hR => ?_, covers_of_all fun R hR => ?_⟩
  · simp only [Proof.Scrypt.blockMixArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, stackArg_entry,
      stackArgAddr_entry,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3, h4, tr, c128]
    exact ⟨trivial, trivial, hds, hsd, hss, had, has, nsrc, ndst, nscr, nsp, trivial, hr⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl
    · exact covers_of_in isrc
    · exact covers_of_in iarg
    · intro a n h
      obtain ⟨R', hR', hc'⟩ := covers_of_in idst a n h
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · intro a n h
      obtain ⟨R', hR', hc'⟩ := covers_of_in iscr a n h
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact covers_of_in idst
    · exact covers_of_in iscr

theorem blockMixSpec : BlockMixSpec Impl.Scrypt.Arm.blockMix := by
  intro s src dst scr r h0 h1 h2 h3 h4 hr hlt hds hsd hss had has nsrc ndst nscr nsp isrc iarg
    idst iscr Q hQ
  have tr : (BitVec.ofNat 32 r).toNat = r := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨p, c₁, c₂⟩ := bm_pre h0 h1 h2 h3 h4 hr hlt hds hsd hss had has nsrc ndst nscr nsp isrc
    iarg idst iscr
  refine WP.callCalls (k := Proof.Scrypt.blockMixArm) BlockMix.blockMix_verified.1 p c₁ c₂ ?_
  intro s₂ hrd hwr hsp' hf hcs _ hpost
  simp only [Proof.Scrypt.blockMixArm, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, tr] at hpost
  exact hQ s₂ hrd hwr hsp' hcs hf hpost

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  sp : s₀.sp = s₀'.sp
  a0 : stackArg s₀ 0 = stackArg s₀' 0

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.rr : rr s₀ = rr s₀' := by simp only [RoMix.rr, hq.r1]
theorem PubEq.NN : NN s₀ = NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.r1, hq.r3]
theorem PubEq.vAt32 (i : Nat) : vAt32 s₀ i = vAt32 s₀' i := by
  simp only [RoMix.vAt32, RoMix.vP, RoMix.rr, hq.r1, hq.r2]
theorem PubEq.tP32 : tP32 s₀ = tP32 s₀' := by simp only [RoMix.tP32, RoMix.sc, hq.a0]

end

/-- The registers the loops keep, with `r9 = bp` and `r8 = q`, and the
memory outside our regions (the stack arguments). -/
structure KR (s₀ : State) (bp q : BitVec 32) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀
  r5 : s.gpr .r5 = vP s₀
  r6 : s.gpr .r6 = sc s₀
  r7 : s.gpr .r7 = BitVec.ofNat 32 (128 * rr s₀)
  r8 : s.gpr .r8 = q
  r9 : s.gpr .r9 = bp
  frame : Frame [bR s₀, vR s₀, scR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9]

theorem kRegs_ne : ∀ r ∈ kRegs, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by decide

theorem kRegs_pres : ∀ r ∈ kRegs, r ∈ preserved ∧ r ≠ .lr ∧ r ∉ linkRegs := by decide

theorem KR.keep {s₀ : State} {bp q : BitVec 32} {s s' : State} (h : KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hk : ∀ r ∈ kRegs, s'.gpr r = s.gpr r) (hf : Frame [bR s₀, vR s₀, scR s₀] s.mem s'.mem) :
    KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hk _ (by decide)).trans h.r4,
    (hk _ (by decide)).trans h.r5, (hk _ (by decide)).trans h.r6, (hk _ (by decide)).trans h.r7,
    (hk _ (by decide)).trans h.r8, (hk _ (by decide)).trans h.r9, h.frame.trans hf⟩

/-- Whether an instruction writes none of `kRegs`. -/
def kFree (i : Instr) : Bool := kRegs.all fun r => dstOf i != some r

/-- `KR` survives code that writes none of its registers. -/
theorem KR.exec {c : Prog isa} (hc : c.allInstrs kFree = true) (hn : c.noFrames = true)
    {s₀ : State} (hw : s₀.wr = [bR s₀, vR s₀, scR s₀]) {bp q : BitVec 32} {s s' : State}
    {t : List Leak} (he : Exec isa c s t s') (h : KR s₀ bp q s) : KR s₀ bp q s' := by
  obtain ⟨rd, wr, sp, f⟩ := Exec.regions he hn
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  refine h.keep rd wr sp (fun r hr => Exec.gpr (fun i hi => ?_) he (.inr (kRegs_pres r hr).2.2)) ?_
  · have := hc i hi
    simp only [kFree, List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this r hr
  · rw [h.wr, hw] at f; exact f

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : Inv2 s₀ i s) :
    KR s₀ (vAt32 s₀ i) (BitVec.ofNat 32 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.r4, h.r5, h.r6, h.r7, h.r8, h.r9, h.frame⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : Inv3 s₀ i s) :
    KR s₀ (BitVec.ofNat 32 (NN s₀ - 1)) (BitVec.ofNat 32 (NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.sp, h.r4, h.r5, h.r6, h.r7, h.r8, h.r9, h.frame⟩

/-- The registers `KR` fixes agree in two runs. -/
theorem agree_K {s₀ s₀' : State} (hq : PubEq s₀ s₀') {bp q bp' q' : BitVec 32} {s s' : State}
    (h : KR s₀ bp q s) (h' : KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs (extra ++ kRegs)) s s' := by
  refine Taint.agree_ofRegs fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, bP, bP, hq.r0]
  · rw [h.r5, h'.r5, vP, vP, hq.r2]
  · rw [h.r6, h'.r6, sc, sc, hq.a0]
  · rw [h.r7, h'.r7, hq.rr]
  · rw [h.r8, h'.r8, hq']
  · rw [h.r9, h'.r9, hbp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = A
  r1 : s.gpr .r1 = BitVec.ofNat 32 (rr s₀)
  r2 : s.gpr .r2 = bP s₀
  r3 : s.gpr .r3 = BitVec.ofNat 32 (rr s₀)

theorem call_pre {s₀ : State} (hp : Pre s₀) {A : BitVec 32} (hA : SrcOK s₀ A) {bp q : BitVec 32}
    {s : State} (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    Proof.Scrypt.blockMixArm.pre (s.callEntry.withRegions
      [⟨State.addr A, 128 * rr s₀⟩, ⟨stackArgAddr s 0, 4⟩]
      [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]) ∧
    Covers ([⟨State.addr A, 128 * rr s₀⟩, ⟨stackArgAddr s 0, 4⟩] ++
      [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] s.wr := by
  have lt := r_lt hp
  have ea := stackArgAddr_eq h.sp
  exact bm_pre ha.r0 ha.r1 ha.r2 ha.r3 (arg_keep hp h.frame h.sp rfl) hp.pos lt
    ((hp.b_s.sub_left (b_sub' (s₀ := s₀))).sub_right (w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [ea]; exact (hp.a_b.sub_left (arg4_sub s₀)).sub_right (b_sub' (s₀ := s₀)))
    (by rw [ea]; exact (hp.a_s.sub_left (arg4_sub s₀)).sub_right (w_sub (s₀ := s₀)))
    hA.nw (by have := hp.b_nw; omega) (by have := hp.s_nw; omega)
    (by rw [h.sp]; have := hp.sp_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr)
    (by rw [ea, h.rd, h.wr]; exact arg_in hp) (by rw [h.wr]; exact b_in hp)
    (by rw [h.wr]; exact w_in hp)

theorem call_wp {s₀ : State} (hp : Pre s₀) {A : BitVec 32} (hA : SrcOK s₀ A) {bp q : BitVec 32}
    {s : State} (h : KR s₀ bp q s) (ha : Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.Arm.blockMix) s (KR s₀ bp q) :=
  bm_call blockMixSpec hp hA ha.r0 ha.r1 ha.r2 ha.r3 h.sp h.rd h.wr h.frame
    fun _ rd wr sp cs f _ => h.keep rd wr sp
      (fun r hr => cs r (kRegs_pres r hr).1 (kRegs_pres r hr).2.1) (call_frame f)

theorem call_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
    {A A' : BitVec 32} (hA : SrcOK s₀ A) (hA' : SrcOK s₀' A') (hAA : A = A')
    {bp q bp' q' : BitVec 32} :
    RelCT isa (fun s s' => (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.Arm.blockMix)
      fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' := by
  subst hAA
  have eb : bP s₀' = bP s₀ := hq.r0.symm
  have es : sc s₀' = sc s₀ := hq.a0.symm
  have er : rr s₀' = rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (KR s₀ bp q s ∧ Args s₀ A s) ∧ (KR s₀' bp' q' s' ∧ Args s₀' A s'))
    BlockMix.blockMix_verified.1 BlockMix.blockMix_verified.2.1
    [⟨State.addr A, 128 * rr s₀⟩, ⟨stackArgAddr s₀ 0, 4⟩]
    [⟨bA s₀, 128 * rr s₀⟩, ⟨scA s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := call_pre hp' hA' h' ha'
      rw [stackArgAddr_eq h.sp] at p₁ c₁
      have ea : stackArgAddr s₀' 0 = stackArgAddr s₀ 0 := by
        rw [stackArgAddr, stackArgAddr, hq.sp]
      rw [stackArgAddr_eq h'.sp, ea] at p₂ c₂
      simp only [bA, scA, eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂⟩
      simp only [Proof.Scrypt.blockMixArm, State.withRegions_gpr, State.withRegions_sp,
        State.callEntry_sp, stackArg_entry,
        State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.r0, ha.r1, ha.r2, ha.r3,
        ha'.r0, ha'.r1, ha'.r2, ha'.r3, eb, er, h.sp, h'.sp, hq.sp,
        arg_keep hp h.frame h.sp rfl, arg_keep hp' h'.frame h'.sp rfl, es]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨call_wp hp hA h.1.1 h.1.2, call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## Relating pieces of code -/

/-- Code that writes none of `kRegs` keeps `KR` in both runs. -/
theorem RelCT.keepK {P : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hc : c.allInstrs kFree = true) (hn : c.noFrames = true) {s₀ s₀' : State}
    (hw : s₀.wr = [bR s₀, vR s₀, scR s₀]) (hw' : s₀'.wr = [bR s₀', vR s₀', scR s₀'])
    {bp q bp' q' : BitVec 32} (hk : ∀ s s', P s s' → KR s₀ bp q s ∧ KR s₀' bp' q' s') :
    RelCT isa P c fun s s' => KR s₀ bp q s ∧ KR s₀' bp' q' s' :=
  fun _ _ _ _ _ _ hp e e' =>
    ⟨(h _ _ _ _ _ _ hp e e').1, KR.exec hc hn hw e (hk _ _ hp).1, KR.exec hc hn hw' e' (hk _ _ hp).2⟩

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

theorem RelCT.assoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ r₁ =>
    cases r₁ with
    | seq b₁ r₁ =>
      cases r₁ with
      | seq c₁ r₁ =>
        cases r₁ with
        | seq d₁ f₁ =>
          cases e₂ with
          | seq a₂ r₂ =>
            cases r₂ with
            | seq b₂ r₂ =>
              cases r₂ with
              | seq c₂ r₂ =>
                cases r₂ with
                | seq d₂ f₂ =>
                  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁)
                    (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
                  simp only [List.append_assoc] at ht
                  exact ⟨ht, hq⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Setting up the calls -/

theorem tail_wp {s₀ : State} (hp : Pre s₀) {bp q A : BitVec 32} {s : State} (h : KR s₀ bp q s)
    (hA : s.gpr .r0 = A) :
    WP isa (.block bmTail) s fun s' => KR s₀ bp q s' ∧ Args s₀ A s' := by
  have lt := r_lt hp
  refine wp_mov (op2_lsr (by decide)) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun d ud => WP.block_nil ⟨?_, ?_⟩
  · exact h.keep (by rw [ud.rd, ub.rd, ua.rd]) (by rw [ud.wr, ub.wr, ua.wr])
      (by rw [ud.sp, ub.sp, ua.sp]) (fun r hr => by
        obtain ⟨-, h1, h2, h3⟩ := kRegs_ne r hr
        rw [ud.other _ h3, ub.other _ h2, ua.other _ h1])
      (by rw [ud.mem, ub.mem, ua.mem]; exact Frame.refl _ _)
  have h1 : a.gpr .r1 = BitVec.ofNat 32 (rr s₀) := by
    rw [ua.gpr, h.r7, shr_ofNat32 _ lt]; congr 1; omega
  exact ⟨by rw [ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [ud.other _ (by decide), ub.other _ (by decide), h1],
    by rw [ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.r4],
    by rw [ud.gpr, ub.other _ (by decide), h1]⟩

theorem x2_wp {s₀ : State} (hp : Pre s₀) {bp q : BitVec 32} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([.mov .r0 (.reg .r9)] ++ bmTail)) s fun s' => KR s₀ bp q s' ∧ Args s₀ bp s' :=
  wp_mov (op2_reg _ _) fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp (fun r hr => ua.other r (kRegs_ne r hr).1)
      (by rw [ua.mem]; exact Frame.refl _ _)) (by rw [ua.gpr, h.r9])

theorem x3_wp {s₀ : State} (hp : Pre s₀) {bp q : BitVec 32} {s : State} (h : KR s₀ bp q s) :
    WP isa (.block ([.dp .add .r0 .r6 (.imm 192)] ++ bmTail)) s
      fun s' => KR s₀ bp q s' ∧ Args s₀ (tP32 s₀) s' :=
  wp_add (op2_imm (by decide)) fun a ua => tail_wp hp
    (h.keep ua.rd ua.wr ua.sp (fun r hr => ua.other r (kRegs_ne r hr).1)
      (by rw [ua.mem]; exact Frame.refl _ _)) (by rw [ua.gpr, h.r6]; rfl)

/-! ## Step 2, in two runs -/

theorem eval_z {s : State} {b : Bool} (h : s.z = b) : isa.eval .ne s = some !b := by
  rw [← h]; exact eval_ne s

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s') (step2 Impl.Scrypt.Arm.blockMix)
      fun s s' => (Inv2 s₀ (i + 1) s ∧ s.z = decide (i + 1 = NN s₀)) ∧
        (Inv2 s₀' (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have ev : vAt32 s₀ i = vAt32 s₀' i := hq.vAt32 i
  have e15 : BitVec.ofNat 32 (NN s₀ - i) = BitVec.ofNat 32 (NN s₀' - i) := by rw [hq.NN]
  let K (t₀ t : State) : Prop := KR t₀ (vAt32 t₀ i) (BitVec.ofNat 32 (NN t₀ - i)) t
  have ac : RelCT isa (fun s s' => Inv2 s₀ i s ∧ Inv2 s₀' i s')
      (.seq (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r9), .mov .r2 (.shifted .r7 .lsr 2)])
        copyLoop)
      fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide))
      (by decide +kernel) (by decide +kernel) hp.wr hp'.wr fun _ _ h => ⟨h.1.kr, h.2.kr⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.mov .r0 (.reg .r9)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (vAt32 s₀ i) s) ∧ (K s₀' s' ∧ Args s₀' (vAt32 s₀' i) s') :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x2_wp hp h.1, x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_v hp hi) (srcOK_v hp' hi') ev
    (bp := vAt32 s₀ i) (q := BitVec.ofNat 32 (NN s₀ - i)) (bp' := vAt32 s₀' i)
    (q' := BitVec.ofNat 32 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block [.dp .add .r9 .r9 (.reg .r7), .subs .r8 .r8 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := RelCT.assoc (ac.seq ((x.seq cl).seq e))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step2_ok blockMixSpec hp hi h.1, step2_ok blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s')
      (.loop (step2 Impl.Scrypt.Arm.blockMix) .ne)
      fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.Arm.blockMix)
    (c := .ne) (Q := fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv2 s₀ i s ∧ Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_z z, eval_z z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3 -/

theorem j_wp {s₀ : State} (hp : Pre s₀) {q : BitVec 32} {s : State}
    (h : KR s₀ (BitVec.ofNat 32 (NN s₀ - 1)) q s) {j : Nat} (hj : jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      KR s₀ (BitVec.ofNat 32 (NN s₀ - 1)) q s' ∧ s'.gpr .r0 = BitVec.ofNat 32 j :=
  WP.mono (j_ok hp h.r4 h.r7 h.r9 h.rd h.wr) fun _ u =>
    ⟨h.keep u.rd u.wr u.sp (fun r hr => u.other r (kRegs_ne r hr).1)
      (by rw [u.mem]; exact Frame.refl _ _), by rw [u.gpr, hj]⟩

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
      (step3 Impl.Scrypt.Arm.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.z = decide (i + 1 = NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  have e1 : BitVec.ofNat 32 (NN s₀ - 1) = BitVec.ofNat 32 (NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 32 (NN s₀ - i) = BitVec.ofNat 32 (NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop :=
    KR t₀ (BitVec.ofNat 32 (NN t₀ - 1)) (BitVec.ofNat 32 (NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (Inv3 s₀ i s ∧ jOf s₀ s.mem = j) ∧
        (Inv3 s₀' i s' ∧ jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .r0 = BitVec.ofNat 32 j) ∧ (K s₀' s' ∧ s'.gpr .r0 = BitVec.ofNat 32 j) :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨j_wp hp h.1.1.kr h.1.2, j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have mx : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .r0 = BitVec.ofNat 32 j) ∧
        (K s₀' s' ∧ s'.gpr .r0 = BitVec.ofNat 32 j))
      (.seq (.block [.mov .r1 (.reg .r5), .mov .r2 (.reg .r7)]) <| .seq mulLoop <|
        .seq (.block [.mov .r0 (.reg .r4), .dp .add .r2 .r6 (.imm 192),
          .mov .r3 (.shifted .r7 .lsr 2)]) xorLoop) fun s s' => K s₀ s ∧ K s₀' s' :=
    RelCT.keepK (RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([.r0] ++ kRegs))
      (fun _ _ h => agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide))
      (by decide +kernel) (by decide +kernel) hp.wr hp'.wr fun _ _ h => ⟨h.1.1, h.2.1⟩
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.dp .add .r0 .r6 (.imm 192)] ++ bmTail)) fun s s' =>
        (K s₀ s ∧ Args s₀ (tP32 s₀) s) ∧ (K s₀' s' ∧ Args s₀' (tP32 s₀') s') :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨x3_wp hp h.1, x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := call_rel hp hp' hq (srcOK_t hp) (srcOK_t hp') hq.tP32
    (bp := BitVec.ofNat 32 (NN s₀ - 1)) (q := BitVec.ofNat 32 (NN s₀ - i))
    (bp' := BitVec.ofNat 32 (NN s₀' - 1)) (q' := BitVec.ofNat 32 (NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.subs .r8 .r8 (.imm 1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs ([] ++ kRegs))
      (fun _ _ h => agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (RelCT.assoc4 (mx.seq ((x.seq cl).seq e)))
  rw [← blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨step3_ok blockMixSpec hp hi h.1.1,
    step3_ok blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (rr s₀) (NN s₀) (B s₀) =
  Spec.Scrypt.roMixIndices (rr s₀') (NN s₀') (B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < NN s₀) :
    RelCT isa (fun s s' => Inv3 s₀ i s ∧ Inv3 s₀' i s') (step3 Impl.Scrypt.Arm.blockMix)
      fun s s' => (Inv3 s₀ (i + 1) s ∧ s.z = decide (i + 1 = NN s₀)) ∧
        (Inv3 s₀' (i + 1) s' ∧ s'.z = decide (i + 1 = NN s₀')) := by
  have hi' : i < NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Nat) => body3_rel_j hp hp' hq hi j).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := drop_js hi h
  obtain ⟨r', hr'⟩ := drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨jOf s₀ s.mem, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s')
      (.loop (step3 Impl.Scrypt.Arm.blockMix) .ne)
      fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.Arm.blockMix)
    (c := .ne) (Q := fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s')
    (fun n s s' => ∃ i, n = NN s₀ - i ∧ i < NN s₀ ∧ Inv3 s₀ i s ∧ Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_z z, eval_z z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ NN s₀ := by simpa using ht'
        exact ⟨NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, NN_pos hp, h.1, h.2⟩) fun _ _ h => h

/-- The prologue's taint: the argument registers and the stack arguments are public. -/
def τPro : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

omit hp' hq hL in
theorem wfPro : VG.Arm.Taint.Wf τPro s₀ := by
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by show s₀.sp.toNat + 4 ≤ 2 ^ 32; have := hp.sp_nw; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  have e : (⟨State.addr s₀.sp, 4⟩ : Region) = ⟨stackArgAddr s₀ 0, 4⟩ := by simp [stackArgAddr]
  simp only [τPro, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.a_b.sub_left (arg4_sub s₀)
  · exact hp.a_v.sub_left (arg4_sub s₀)
  · exact hp.a_s.sub_left (arg4_sub s₀)

omit hL in
theorem agreePro : VG.Arm.Taint.Agree τPro s₀ s₀' := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wfPro hp, wfPro hp',
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hq.sp,
    fun k hk => ?_⟩
  · simp only [τPro, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hq.r0
    · exact hq.r1
    · exact hq.r2
    · exact hq.r3
  · simp only [τPro] at hk
    rw [BlockMix.argByte_eq, BlockMix.argByte_eq, Mem.readW_byte s₀.mem _ hk,
      Mem.readW_byte s₀'.mem _ hk]
    exact congrArg _ hq.a0

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.Arm.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.Arm.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => P1 s₀ s ∧ P1 s₀' s' :=
    ((RelCT.taint (A := taint) τPro (P := fun s s' => s = s₀ ∧ s' = s₀')
      (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact agreePro hp hp' hq)
      (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := P1 s₀) (F₂ := P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => P1 s₀ s ∧ P1 s₀' s') nLoop fun s s' => N1 s₀ s ∧ N1 s₀' s' :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r0, .r1, .r2])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.r0, h'.r0, hq.rr]
        · rw [h.r1, h'.r1]
        · rw [h.r2, h'.r2, RoMix.vl, RoMix.vl, hq.r3]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨nloop_ok hp h.1, nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => N1 s₀ s ∧ N1 s₀' s') (.block rmSetup)
      fun s s' => Inv2 s₀ 0 s ∧ Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r1, .r5, .r6])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.r1, h'.r1, hq.NN]
        · rw [h.r5, h'.r5, vP, vP, hq.r2]
        · rw [h.r6, h'.r6, sc, sc, hq.a0]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨setup2_ok hp h.1, setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => Inv2 s₀ (NN s₀) s ∧ Inv2 s₀' (NN s₀') s') (.block rmMid)
      fun s s' => Inv3 s₀ 0 s ∧ Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r6])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.r6, h'.r6, sc, sc, hq.a0]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨mid_ok hp h.1, mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv3 s₀ (NN s₀) s ∧ Inv3 s₀' (NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (VG.Arm.Taint.ofRegs [.r6])
      (fun _ _ h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.r6, h.2.r6, sc, sc, hq.a0]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((loop2_rel hp hp' hq).seq
    (md.seq ((loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixArm.pub s₁ s₂) : PubEq s₁ s₂ :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.1, h.2.2.2.2.2.1⟩

/-- No instruction of ROMix, or of the functions it calls, writes `r10` or `r11`. -/
theorem others_kept :
    (instrs Impl.Scrypt.Arm.roMix).all
      (fun i => [Reg.r10, .r11].all fun r => dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem preserved_cases :
    ∀ r ∈ preserved, r ∈ rmSaved.map Prod.fst ∨ r ∈ [Reg.r10, .r11] := by
  decide

/-- A state satisfying the precondition: `b` at `0x1000`, `v` at `0x2000`
(`N = 1`) and the scratch space at `0x3000` (384 bytes), passed on the stack
at `0x5000` with its length in 128-byte blocks. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x30 else if a = 0x5004 then 3 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_verified : Verified Arm.target Impl.Scrypt.Arm.roMix Proof.Scrypt.roMixArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, hk, hsp, hpost⟩ := correct blockMixSpec (pre_of hs)
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, hpost⟩
    rcases preserved_cases r hr with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact hk p hp
    · have hc := others_kept
      rw [List.all_eq_true] at hc
      refine Exec.gpr (fun i hi => ?_) he (.inr (by revert h; revert r; decide))
      have := hc i hi
      simp only [List.all_eq_true, bne_iff_ne, ne_eq] at this
      exact this r h
  · intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
    exact (roMix_rel (pre_of h₁) (pre_of h₂) (pubEq_of hpub) hpub.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  · have e0 : stackArg satState 0 = 0x3000 := by decide
    have e1 : stackArg satState 1 = 3 := by decide
    refine ⟨satState, ?_⟩
    simp only [Proof.Scrypt.roMixArm, e0, e1]
    refine ⟨by simp [satState, stackArgAddr]; decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, by decide, by decide, by decide, ⟨0, rfl⟩, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState, stackArgAddr, State.addr] at h₁ h₂
      bv_omega

end VG.Proof.Scrypt.Arm.RoMix
