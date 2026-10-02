import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Loop
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: constant time

Untrusted: everything here is checked by Lean. As on x86
(`Proof/Pbkdf2/Whole/X86/CT.lean`): the pieces of code between the calls are
checked by the taint analysis (`Checks`, which the kernel evaluates for each
hash function), with the stack arguments and the registers holding pointers,
lengths and, in the loop over the blocks, the bytes written public
(`piece`); the calls are related by their contracts (`init_rel`, `upd_rel`,
`fin_rel`, `hi_rel`, `hf_rel`, `it_rel`), whose public arguments are the
same in two runs with the same public arguments (`PubEq`). The branches
(whether the password is hashed, and the loop over the blocks) depend only
on the lengths.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Hmac.Generic.Arm (Hash scrAt copy)
open VG.Proof.Hmac.Generic.Arm (HashOK count FinArgs init_rel fin_rel)
open VG.Proof.MdStream.Arm (eval_eq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the stack arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs 16) c hc).isSome = true

/-- The argument registers; the registers public in the key, while hashing
the password, from the key on, and in the loop over the blocks. -/
abbrev inRegs : List Reg := [.r0, .r1, .r2, .r3]
abbrev kkRegs : List Reg := [.r5, .r6, .r8, .r9, .r11]
abbrev hkRegs : List Reg := [.r4, .r5, .r6, .r8, .r9, .r11]
abbrev krRegs : List Reg := [.r5, .r6, .r11]
abbrev lpRegs : List Reg := [.r4, .r5, .r6, .r11]

/-- The taint checks of the pieces of `pbkdf2` between its calls. -/
structure Checks (F : Fns) : Prop where
  pro : Ck inRegs (.block F.prologue)
  cmp : Ck kkRegs (.block F.cmpPw)
  hk1 : Ck kkRegs (.block (scrAt .r4 F.stWO))
  hk2 : Ck hkRegs (.block [.mov .r0 (.reg .r4)])
  hk3 : Ck hkRegs (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
    .mov .r2 (.imm 0), .mov .r3 (.imm 0)])
  hk5 : Ck hkRegs (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 F.hkO ++ [.mov .r12 (.reg .r11), .mov .r2 (.reg .r9),
    .mov .r3 (.imm 0)]))
  hk7 : Ck krRegs (.block (scrAt .r2 F.hkO ++ [.movw .r3 (BitVec.ofNat 16 F.H.D)]))
  short : Ck kkRegs (.block [.mov .r2 (.reg .r8), .mov .r3 (.reg .r9)])
  su1 : Ck krRegs (.block F.initArgs)
  su3 : Ck krRegs (copy .r11 F.st0O .r11 F.stSO F.H.S)
  su4 : Ck krRegs (.block F.saltArgs)
  init : Ck krRegs (.block F.loopInit)
  skip : Ck lpRegs (.block [])
  b1 : Ck lpRegs (copy .r11 F.stSO .r11 F.stWO F.H.S)
  b2 : Ck lpRegs (.block F.updArgs)
  b4 : Ck lpRegs (.block F.finArgs)
  b6 : Ck lpRegs (copy .r11 F.uO .r11 F.tO F.H.D)
  b7 : Ck lpRegs (.block F.iterArgs)
  tail : Ck lpRegs (.seq F.outLen (.seq F.outLoop (.block F.advance)))
  restore : Ck krRegs (.block F.L.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1
  a2 : stackArg s₀ 2 = stackArg s₀' 2
  a3 : stackArg s₀ 3 = stackArg s₀' 3

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 4) : stackArg s₀ i = stackArg s₀' i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact hq.a0
  · exact hq.a1
  · exact hq.a2
  · exact hq.a3

/-- `s₀'`'s public values are `s₀`'s. -/
macro "pub_simp" hq:term " at " h:ident : tactic => `(tactic|
  simp only [dO, A, scr, pw, salt, pwl, sl, ol, cc, out, kp, kl, nbk, dn, ← PubEq.r0 $hq, ← PubEq.r1 $hq,
    ← PubEq.r2 $hq, ← PubEq.r3 $hq, ← PubEq.a0 $hq, ← PubEq.a1 $hq, ← PubEq.a2 $hq, ← PubEq.a3 $hq] at $h:ident)

theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a3.symm
theorem PubEq.pwlEq : pwl s₀' = pwl s₀ := by show (s₀'.gpr .r1).toNat = _; rw [← hq.r1]
theorem PubEq.olEq : ol s₀' = ol s₀ := by show (stackArg s₀' 2).toNat = _; rw [← hq.a2]
theorem PubEq.nbkEq : nbk F s₀' = nbk F s₀ := by show Whole.nb _ (ol s₀') = _; rw [hq.olEq]
theorem PubEq.dnEq (k : Nat) : dn F s₀' k = dn F s₀ k := by show Whole.done _ (ol s₀') k = _; rw [hq.olEq]

end

/-- The stack arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre F t) {s : State} (hsp : s.sp = t.sp) (hwr : s.wr = t.wr) :
    s.sp.toNat + 16 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 16⟩ r := by
  have e : (⟨State.addr s.sp, 16⟩ : Region) = argR t := by simp [stackArgAddr, hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact h.o_a.symm
  · exact h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- Two states agree on the taint `argTaint rs 16`. -/
theorem agree {rs : List Reg} {s s' : State} (hk : KR F s₀ s) (hk' : KR F s₀' s')
    (hag : ∀ r ∈ rs, s.gpr r = s'.gpr r) : VG.Arm.Taint.Agree (argTaint rs 16) s s' :=
  agree_argTaint hag (by rw [hk.sp, hk'.sp, hq.sp]) (args_out hp hk.sp hk.wr) (args_out hp' hk'.sp hk'.wr)
    (argMem_of (j := 4) (by rw [hk.sp, hk'.sp, hq.sp]) (by rw [hk.sp]; exact hp.spf) fun i hi => by
      rw [hk.stackArg hp hi, hk'.stackArg hp' hi, hq.a hi])

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree hp hp' hq (hk h) (hk h') (hag s s' h h')) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_kr {s s' : State} (h : KR F s₀ s) (h' : KR F s₀' s') : ∀ r ∈ krRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, salt, salt, hq.r2]
  · rw [h.r6, h'.r6, hq.r3]
  · rw [h.r11, h'.r11, hq.scrEq]

omit hp hp' in
theorem ag_kk {s s' : State} (h : KK F s₀ s) (h' : KK F s₀' s') : ∀ r ∈ kkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ag_kr hq h.kr h'.kr _ (by simp)
  · exact ag_kr hq h.kr h'.kr _ (by simp)
  · rw [h.r8, h'.r8, pw, pw, hq.r0]
  · rw [h.r9, h'.r9, hq.r1]
  · exact ag_kr hq h.kr h'.kr _ (by simp)

omit hp hp' in
theorem ag_hk {s s' : State} (h : KK F s₀ s) (h' : KK F s₀' s') (h4 : s.gpr .r4 = dO s₀ F.stWO)
    (h4' : s'.gpr .r4 = dO s₀' F.stWO) : ∀ r ∈ hkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [hkRegs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h4, h4', dO, dO, hq.scrEq]
  · exact ag_kk hq h h' _ (by simpa using hr)

end

/-! ## The key -/

/-- The password is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ pwl t₀

/-- The pieces of hashing the password. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2a (F : Fns) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = pw t₀ ∧
    s.gpr .r7 = t₀.gpr .r1 ∧ s.gpr .r10 = scr t₀ ∧ count s = BitVec.ofNat 64 0 ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem (State.addr (pw t₀)) (pwl t₀))) ∧ Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.hkO ∧ s.gpr .r12 = scr t₀ ∧
    count s = BitVec.ofNat 64 (pwl t₀) ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem (State.addr (pw t₀)) (pwl t₀))) ∧ Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem (State.addr (pw t₀)) (pwl t₀))) ∧
    Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop := KK F t₀ s ∧ s.z = decide (pwl t₀ < F.H.B + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀') (hc : Checks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (KK F s₀ s ∧ Long F s₀) ∧ (KK F s₀' s' ∧ Long F s₀')) F.hashKey
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D; have := hz.S; have := hz.reach
  unfold Fns.hashKey Hash.callInit
  have r1 := piece hp hp' hq (fun t₀ s => KK F t₀ s ∧ Long F t₀) (Hk1 F) (fun h => h.1.kr)
    (fun s s' h h' => ag_kk hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (hk1_ok h.1 (by omega)) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2a := piece hp hp' hq (Hk1 F) (Hk2a F) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2 h'.1.2) hc.hk2
    (fun _ s h => WP.mono (hk2a_ok h.1.1 h.1.2) fun t ⟨k, d, a⟩ => ⟨⟨k, d, a⟩, h.2⟩)
  have cw : ∀ {t₀ : State}, Pre F t₀ → ∀ {s : State}, KR F t₀ s →
      Covers [⟨State.addr (dO t₀ F.stWO), F.H.S⟩] s.wr := fun {t₀} hp₀ {s} k => by
    rw [dO_addr hp₀ (by omega)]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp₀ k (by omega)
  have r2 : RelCT isa (fun s s' => Hk2a F s₀ s ∧ Hk2a F s₀' s') (.call F.H.initN F.H.initC)
      fun s s' => Hk2 hF.hH s₀ s ∧ Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, _, a⟩, _⟩, ⟨⟨k', _, a'⟩, _⟩⟩ =>
        ⟨a, by rw [a', dO, dO, hq.scrEq], by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega, cw hp k.kr,
          by have := cw hp' k'.kr; rw [dO, hq.scrEq] at this; exact this⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (hk2b_ok hp hz hF.hH k d a) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (hk2b_ok hp' hz hF.hH k d a) fun t h => ⟨h, l⟩)
  have r3 := piece hp hp' hq (Hk2 hF.hH) (Hk3 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2.2 h'.1.2.2) hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk3_ok k d) fun t ⟨k', d', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨k', d', a₀, a₁, a₇, a₁₀, c, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => Hk3 hF.hH s₀ s ∧ Hk3 hF.hH s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => Hk4 hF.hH s₀ s ∧ Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp)
        fun s s' ⟨⟨⟨k, _, a₀, a₁, a₇, a₁₀, c, _⟩, _⟩, ⟨⟨k', _, a₀', a₁', a₇', a₁₀', c', _⟩, _⟩⟩ =>
        ⟨hk4_args hp hz hF.hH k a₀ a₁ a₇ a₁₀,
          by have := hk4_args hp' hz hF.hH k' a₀' a₁' a₇' a₁₀'; pub_simp hq at this; exact this,
          by rw [c, c'], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (hk4_ok hp hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (hk4_ok hp' hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
  have r5 := piece hp hp' hq (Hk4 hF.hH) (Hk5 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2.1 h'.1.2.1) hc.hk5
    (fun hp₀ s ⟨⟨k, d, r⟩, l⟩ => WP.mono (hk5_ok k d (by omega)) fun t ⟨k', a₀, a₁, a₁₂, c, m⟩ =>
      ⟨⟨k', a₀, a₁, a₁₂, c, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => Hk5 hF.hH s₀ s ∧ Hk5 hF.hH s₀' s')
      (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8))
      fun s s' => Hk6 hF.hH s₀ s ∧ Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := s₀.sp) fun s s' ⟨⟨⟨k, a₀, a₁, a₁₂, c, _⟩, _⟩, ⟨⟨k', a₀', a₁', a₁₂', c', _⟩, _⟩⟩ =>
        ⟨hk6_args hp hz hF.hH k a₀ a₁ a₁₂,
          by have := hk6_args hp' hz hF.hH k' a₀' a₁' a₁₂'; pub_simp hq at this; exact this,
          by rw [c, c', hq.pwlEq], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (hk6_ok hp hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (hk6_ok hp' hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
  have r7 := piece hp hp' hq (Hk6 hF.hH) (Keyed hF) (fun h => h.1.1) (fun s s' h h' => ag_kr hq h.1.1 h'.1.1) hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (hk7_ok k (by omega) (by omega)) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ pwl t₀ < F.H.B + 1 := by omega
      have ekp : kp F t₀ = dO t₀ F.hkO := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = F.H.D := by simp only [kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ (by omega), m, b, blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega)
        (hash_len hF.hH b)])
  exact (r1.seq ((r2a.seq r2).seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ h => h

theorem key_rel :
    RelCT isa (fun s s' => KK F s₀ s ∧ KK F s₀' s') F.key fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.key
  have rc := piece hp hp' hq (fun t₀ s => KK F t₀ s) (Cmp F) (fun h => h.kr) (fun s s' h h' => ag_kk hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (cmp_ok hz k) fun t ⟨k', z, _⟩ => ⟨k', z⟩)
  have ev : ∀ {t₀ t : State}, Cmp F t₀ t → isa.eval .eq t = some (decide (pwl t₀ < F.H.B + 1)) := by
    intro t₀ t h
    show eval .eq t = _
    rw [eval_eq, h.2]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.pwlEq]) ?_ ?_)
  · refine (piece hp hp' hq (fun t₀ s => Cmp F t₀ s ∧ pwl t₀ < F.H.B + 1) (Keyed hF) (fun h => h.1.1.kr)
      (fun s s' h h' => ag_kk hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : kp F t₀ = pw t₀ := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = pwl t₀ := by simp only [kl, hlt, ↓reduceIte]
      refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ =>
        VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₃ u₃ => WP.block_nil
          ⟨(k.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr, k.r8, ekp]
      · rw [u₃.gpr, u₂.other _ (by decide), k.r9, ekl, ofNat_toNat32]
      · rw [u₃.mem, u₂.mem, ekp, ekl, k.kr.pwBytes hp₀]
    · have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      exact ⟨⟨h.1.1, this⟩, h.1.2, by rw [hq.pwlEq]; exact this⟩
  · refine (hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, by omega⟩, h.1.2.1, by show F.H.B + 1 ≤ pwl s₀'; rw [hq.pwlEq]; omega⟩

end

/-! ## HMAC's states for the key, and the salt -/

abbrev Su1 (hF : FnsOK F) (t₀ s : State) : Prop :=
  Keyed hF t₀ s ∧ s.gpr .r0 = dO t₀ F.st0O ∧ s.gpr .r1 = dO t₀ F.st1O ∧ s.gpr .r12 = scr t₀
abbrev Su2 (hF : FnsOK F) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (K0 hF t₀) opad) ∧ (K0 hF t₀).length = F.H.B
abbrev Su3 (hF : FnsOK F) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.stSO) (xorPad (K0 hF t₀) ipad) ∧ (K0 hF t₀).length = F.H.B
abbrev Su4 (hF : FnsOK F) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .r0 = dO t₀ F.stSO ∧ s.gpr .r1 = salt t₀ ∧ s.gpr .r7 = t₀.gpr .r3 ∧
    s.gpr .r10 = scr t₀ ∧ count s = BitVec.ofNat 64 F.H.B) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.stSO) (xorPad (K0 hF t₀) ipad) ∧ (K0 hF t₀).length = F.H.B
/-- After the setup. -/
abbrev Su5 (hF : FnsOK F) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ States hF t₀ s.mem ∧ (K0 hF t₀).length = F.H.B

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀') (hc : Checks F)
include hp hp' hq hc

theorem setup_rel :
    RelCT isa (fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s') F.setup fun s s' => Su5 hF s₀ s ∧ Su5 hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.setup
  have r1 := piece hp hp' hq (Keyed hF) (Su1 hF) (fun h => h.kr) (fun s s' h h' => ag_kr hq h.kr h'.kr) hc.su1
    (fun _ s h => su1_ok hz hF h)
  have r2 : RelCT isa (fun s s' => Su1 hF s₀ s ∧ Su1 hF s₀' s')
      (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8))
      fun s s' => Su2 hF s₀ s ∧ Su2 hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := s₀.sp) fun s s' ⟨⟨h, a₀, a₁, a₁₂⟩, ⟨h', a₀', a₁', a₁₂'⟩⟩ =>
        ⟨su2_args hp hz hF h a₀ a₁ a₁₂,
          by have := su2_args hp' hz hF h' a₀' a₁' a₁₂'; pub_simp hq at this; exact this,
          h.kr.sp, by rw [h'.kr.sp, hq.sp]⟩)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => WP.mono (su2_ok hp hz hF h a₀ a₁ a₁₂) fun t ⟨k, r0, r1⟩ =>
        ⟨k, r0, r1, K0_length hp hz hF h⟩)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => WP.mono (su2_ok hp' hz hF h a₀ a₁ a₁₂) fun t ⟨k, r0, r1⟩ =>
        ⟨k, r0, r1, K0_length hp' hz hF h⟩)
  have r3 := piece hp hp' hq (Su2 hF) (Su3 hF) (fun h => h.1) (fun s s' h h' => ag_kr hq h.1 h'.1) hc.su3
    (fun hp₀ s ⟨k, r0, r1, l⟩ => WP.mono (su3_ok hp₀ hz hF k r0 r1) fun t ⟨k', r0', r1', rS⟩ =>
      ⟨k', r0', r1', rS, l⟩)
  have r4 := piece hp hp' hq (Su3 hF) (Su4 hF) (fun h => h.1) (fun s s' h h' => ag_kr hq h.1 h'.1) hc.su4
    (fun hp₀ s ⟨k, r0, r1, rS, l⟩ => WP.mono (su4_ok hz k) fun t ⟨k', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨k', a₀, a₁, a₇, a₁₀, c⟩, m ▸ r0, m ▸ r1, m ▸ rS, l⟩)
  have r5 : RelCT isa (fun s s' => Su4 hF s₀ s ∧ Su4 hF s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => Su5 hF s₀ s ∧ Su5 hF s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp) fun s s' ⟨⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, _⟩, ⟨⟨k', a₀', a₁', a₇', a₁₀', c'⟩, _⟩⟩ =>
        ⟨su5_args hp hz hF k a₀ a₁ a₇ a₁₀,
          by have := su5_args hp' hz hF k' a₀' a₁' a₇' a₁₀'; pub_simp hq at this; exact this,
          by rw [c, c'], k.sp, by rw [k'.sp, hq.sp]⟩)
      (fun s ⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, r0, r1, rS, l⟩ => WP.mono (su5_ok hp hz hF k a₀ a₁ a₇ a₁₀ c l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
      (fun s ⟨⟨k, a₀, a₁, a₇, a₁₀, c⟩, r0, r1, rS, l⟩ => WP.mono (su5_ok hp' hz hF k a₀ a₁ a₇ a₁₀ c l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
  exact r1.seq (r2.seq (r3.seq (r4.seq r5)))

theorem loopInit_rel :
    RelCT isa (fun s s' => Su5 hF s₀ s ∧ Su5 hF s₀' s') (.block F.loopInit) fun s s' =>
      (Inv hF s₀ 0 s ∧ s.z = decide (ol s₀ = 0)) ∧ (Inv hF s₀' 0 s' ∧ s'.z = decide (ol s₀' = 0)) :=
  piece hp hp' hq (Su5 hF) (fun t₀ s => Inv hF t₀ 0 s ∧ s.z = decide (ol t₀ = 0)) (fun h => h.1)
    (fun _ _ h h' => ag_kr hq h.1 h'.1) hc.init
    (fun hp₀ _ ⟨k, st, l⟩ => loopInit_ok hp₀ hF.sizes k st l)

end

/-! ## A block of the output -/

/-- The pieces of a block. -/
abbrev Bk (hF : FnsOK F) (k : Nat) (P : State → State → Prop) (t₀ s : State) : Prop :=
  (Inv hF t₀ k s ∧ P t₀ s) ∧ k < nbk F t₀
abbrev Bk1 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀)
abbrev Bk2 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  (s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.intO ∧ s.gpr .r7 = BitVec.ofNat 32 4 ∧ s.gpr .r10 = scr t₀ ∧
    count s = BitVec.ofNat 64 (F.H.B + (sl t₀ + 0))) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀)
abbrev Bk3 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk4 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  (s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.st1O ∧ s.gpr .r10 = dO t₀ F.uO ∧ s.gpr .r12 = scr t₀ ∧
    count s = BitVec.ofNat 64 (F.H.B + (sl t₀ + 4))) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk5 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  bytesAt s.mem (A t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk6 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  bytesAt s.mem (A t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (A t₀ F.tO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk7 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  (s.gpr .r0 = dO t₀ F.st0O ∧ s.gpr .r1 = dO t₀ F.uO ∧ s.gpr .r3 = dO t₀ F.tO ∧ s.gpr .r2 = stackArg t₀ 0 - 1 ∧
    s.gpr .r12 = scr t₀) ∧
  bytesAt s.mem (A t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (A t₀ F.tO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk8 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s => bytesAt s.mem (A t₀ F.tO) F.H.D = Tk hF t₀ (k + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀') (hc : Checks F)
include hp hp' hq hc

omit hp hp' hc in
theorem ag_loop {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (h' : Inv hF s₀' k s') :
    ∀ r ∈ lpRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [lpRegs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h.r4, h'.r4, hq.dnEq]
  · exact ag_kr hq h.kr h'.kr _ (by simpa using hr)

theorem block_rel (k : Nat) :
    RelCT isa (fun s s' => (Inv hF s₀ k s ∧ k < nbk F s₀) ∧ (Inv hF s₀' k s' ∧ k < nbk F s₀')) F.block
      fun s s' => (Inv hF s₀ (k + 1) s ∧ s.z = decide (k + 1 = nbk F s₀)) ∧
        (Inv hF s₀' (k + 1) s' ∧ s'.z = decide (k + 1 = nbk F s₀')) := by
  have hz := hF.sizes
  unfold Fns.block
  have r1 := piece hp hp' hq (fun t₀ s => Inv hF t₀ k s ∧ k < nbk F t₀) (Bk1 hF k) (fun h => h.1.kr)
    (fun _ _ h h' => ag_loop hq h.1 h'.1) hc.b1
    (fun hp₀ _ ⟨i, l⟩ => WP.mono (b1_ok hp₀ hz i) fun _ ⟨i', r⟩ => ⟨⟨i', r⟩, l⟩)
  have r2 := piece hp hp' hq (Bk1 hF k) (Bk2 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b2
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (b2_ok hp₀ hz i) fun _ ⟨i', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨i', ⟨a₀, a₁, a₇, a₁₀, c⟩, by rw [m]; exact r⟩, l⟩)
  have r3 : RelCT isa (fun s s' => Bk2 hF k s₀ s ∧ Bk2 hF k s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => Bk3 hF k s₀ s ∧ Bk3 hF k s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp)
        fun s s' ⟨⟨⟨i, ⟨a₀, a₁, a₇, a₁₀, c⟩, _⟩, _⟩, ⟨⟨i', ⟨a₀', a₁', a₇', a₁₀', c'⟩, _⟩, _⟩⟩ =>
        ⟨b3_args hp hz i a₀ a₁ a₇ a₁₀,
          by have := b3_args hp' hz i' a₀' a₁' a₇' a₁₀'; pub_simp hq at this; exact this,
          by rw [c, c', sl, sl, hq.r3], i.kr.sp, by rw [i'.kr.sp, hq.sp]⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₇, a₁₀, c⟩, r⟩, l⟩ => WP.mono (b3_ok hp hz i a₀ a₁ a₇ a₁₀ c r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₇, a₁₀, c⟩, r⟩, l⟩ => WP.mono (b3_ok hp' hz i a₀ a₁ a₇ a₁₀ c r) fun _ h => ⟨h, l⟩)
  have r4 := piece hp hp' hq (Bk3 hF k) (Bk4 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b4
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (b4_ok hp₀ hz i) fun _ ⟨i', a₀, a₁, a₁₀, a₁₂, c, m⟩ =>
      ⟨⟨i', ⟨a₀, a₁, a₁₀, a₁₂, c⟩, by rw [m]; exact r⟩, l⟩)
  have r5 : RelCT isa (fun s s' => Bk4 hF k s₀ s ∧ Bk4 hF k s₀' s')
      (.frame (.push [.r10, .r12]) (.call F.hfN F.hfC) (.pop .r12 8))
      fun s s' => Bk5 hF k s₀ s ∧ Bk5 hF k s₀' s' :=
    rel_wp (hf_rel hF.hf (sp := s₀.sp)
        fun s s' ⟨⟨⟨i, ⟨a₀, a₁, a₁₀, a₁₂, c⟩, _⟩, _⟩, ⟨⟨i', ⟨a₀', a₁', a₁₀', a₁₂', c'⟩, _⟩, _⟩⟩ => by
        have cc : count s = count s' := by rw [c, c', sl, sl, hq.r3]
        obtain ⟨c3, c2⟩ := BitVec.append_32_inj cc
        exact ⟨b5_args hp hz i a₀ a₁ a₁₀ a₁₂,
          by have := b5_args hp' hz i' a₀' a₁' a₁₀' a₁₂'; pub_simp hq at this; exact this,
          c2, c3, i.kr.sp, by rw [i'.kr.sp, hq.sp]⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₁₀, a₁₂, c⟩, r⟩, l⟩ => WP.mono (b5_ok hp hz i a₀ a₁ a₁₀ a₁₂ c r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₁₀, a₁₂, c⟩, r⟩, l⟩ => WP.mono (b5_ok hp' hz i a₀ a₁ a₁₀ a₁₂ c r) fun _ h => ⟨h, l⟩)
  have r6 := piece hp hp' hq (Bk5 hF k) (Bk6 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b6
    (fun hp₀ _ ⟨⟨i, u⟩, l⟩ => WP.mono (b6_ok hp₀ hz i u) fun _ ⟨i', u', t'⟩ => ⟨⟨i', u', t'⟩, l⟩)
  have r7 := piece hp hp' hq (Bk6 hF k) (Bk7 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b7
    (fun hp₀ _ ⟨⟨i, u, t⟩, l⟩ => WP.mono (b7_ok hp₀ hz i) fun _ ⟨i', a₀, a₁, a₃, a₂, a₁₂, m⟩ =>
      ⟨⟨i', ⟨a₀, a₁, a₃, a₂, a₁₂⟩, by rw [m]; exact u, by rw [m]; exact t⟩, l⟩)
  have r8 : RelCT isa (fun s s' => Bk7 hF k s₀ s ∧ Bk7 hF k s₀' s')
      (.frame (.push [.r12, .lr]) (.call F.itN F.itC) (.pop .r12 8))
      fun s s' => Bk8 hF k s₀ s ∧ Bk8 hF k s₀' s' :=
    rel_wp (it_rel hF.it (sp := s₀.sp)
        fun s s' ⟨⟨⟨i, ⟨a₀, a₁, a₃, a₂, a₁₂⟩, _⟩, _⟩, ⟨⟨i', ⟨a₀', a₁', a₃', a₂', a₁₂'⟩, _⟩, _⟩⟩ =>
        ⟨b8_args hp hz i a₀ a₁ a₃ a₂ a₁₂,
          by have := b8_args hp' hz i' a₀' a₁' a₃' a₂' a₁₂'; pub_simp hq at this; exact this,
          i.kr.sp, by rw [i'.kr.sp, hq.sp]⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₃, a₂, a₁₂⟩, u, t⟩, l⟩ => WP.mono (b8_ok hp hz i a₀ a₁ a₃ a₂ a₁₂ u t) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨a₀, a₁, a₃, a₂, a₁₂⟩, u, t⟩, l⟩ => WP.mono (b8_ok hp' hz i a₀ a₁ a₃ a₂ a₁₂ u t) fun _ h => ⟨h, l⟩)
  have r9 := piece hp hp' hq (Bk8 hF k) (fun t₀ s => Inv hF t₀ (k + 1) s ∧ s.z = decide (k + 1 = nbk F t₀))
    (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.tail
    (fun hp₀ _ ⟨⟨i, t⟩, l⟩ => tail_ok hp₀ hz l i t)
  exact (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono (fun _ _ h => h)
    fun _ _ h => h

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LoopI (hF : FnsOK F) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  ∃ k, n = nbk F s₀ - k ∧ k < nbk F s₀ ∧ Inv hF s₀ k s ∧ Inv hF s₀' k s'

theorem step_rel (n : Nat) :
    RelCT isa (LoopI hF s₀ s₀' n) F.block fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → Inv hF s₀ (nbk F s₀) s ∧ Inv hF s₀' (nbk F s₀') s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LoopI hF s₀ s₀' m s s') := by
  rintro s₁ s₂ t₁ t₂ s₁' s₂' ⟨k, rfl, hk, i, i'⟩ e₁ e₂
  obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := block_rel hp hp' hq hc k _ _ _ _ _ _
    ⟨⟨i, hk⟩, ⟨i', by rw [hq.nbkEq]; exact hk⟩⟩ e₁ e₂
  refine ⟨ht, ?_⟩
  show isa.eval .ne s₁' = isa.eval .ne s₂' ∧ _
  have e : isa.eval .ne s₁' = some (!decide (k + 1 = nbk F s₀)) := by
    show some (!s₁'.z) = _; rw [z]
  have e' : isa.eval .ne s₂' = some (!decide (k + 1 = nbk F s₀)) := by
    show some (!s₂'.z) = _; rw [z', hq.nbkEq]
  rw [e, e']
  refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
  · have hl : k + 1 = nbk F s₀ := by simpa using hf
    exact ⟨hl ▸ j, by rw [hq.nbkEq, ← hl]; exact j'⟩
  · have hl : k + 1 ≠ nbk F s₀ := by simpa using ht
    exact ⟨nbk F s₀ - (k + 1), by omega, k + 1, rfl, by omega, j, j'⟩

theorem loop_rel :
    RelCT isa (fun s s' => (Inv hF s₀ 0 s ∧ s.z = decide (ol s₀ = 0)) ∧
        (Inv hF s₀' 0 s' ∧ s'.z = decide (ol s₀' = 0)))
      (.ite .eq (.block []) (.loop F.block .ne))
      fun s s' => Inv hF s₀ (nbk F s₀) s ∧ Inv hF s₀' (nbk F s₀') s' := by
  have hD := hF.sizes.D
  have e0 : nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  have ev : ∀ {t : State} {o : Nat}, t.z = decide (o = 0) → isa.eval .eq t = some (decide (o = 0)) :=
    fun h => by show eval .eq _ = _; rw [eval_eq, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hq.olEq]) ?_ ?_
  · by_cases e : ol s₀ = 0
    · have n0 : nbk F s₀ = 0 := e0.2 e
      have n0' : nbk F s₀' = 0 := by rw [hq.nbkEq]; exact n0
      exact (piece hp hp' hq (fun t₀ s => (Inv hF t₀ 0 s ∧ s.z = decide (ol t₀ = 0)) ∧ ol t₀ = 0)
        (fun t₀ s => Inv hF t₀ (nbk F t₀) s) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.skip
        (fun {t₀} _ _ h => WP.block_nil (by
          have : nbk F t₀ = 0 := (Whole.nb_zero hD.1).2 h.2
          rw [this]; exact h.1.1))).mono
        (fun _ _ h => ⟨⟨h.1.1, e⟩, h.1.2, by rw [hq.olEq]; exact e⟩) fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopI hF s₀ s₀') (step_rel hp hp' hq hc) (nbk F s₀ - 0)).mono
      (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : ol s₀ ≠ 0 := by simpa using z
    have : nbk F s₀ ≠ 0 := fun h => e (e0.1 h)
    exact ⟨0, rfl, by omega, h.1.1.1, h.1.2.1⟩

include hF in
/-- `pbkdf2` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.pbkdf2 fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := KK F s₀) (G' := KK F s₀')
    (argTaint inRegs 16) (fun s s' e e' => by
        subst e e'
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          (argMem_of (j := 4) hq.sp hp.spf fun i hi => hq.a hi)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hF s₀ (nbk F s₀) s ∧ Inv hF s₀' (nbk F s₀') s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint krRegs 16)
      (fun s s' h => agree hp hp' hq h.1.kr h.2.kr (ag_kr hq h.1.kr h.2.kr)) hr
  unfold Fns.pbkdf2
  exact pro.seq ((key_rel hp hp' hq hc).seq ((setup_rel hp hp' hq hc).seq ((loopInit_rel hp hp' hq hc).seq
    ((loop_rel hp hp' hq hc).seq restore))))

end

/-- The public arguments of the shared contract. -/
theorem pub_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State}
    (h : (Spec.Pbkdf2.pbkdf2Contract S W Arm.abi 24).pub s₁ s₂) : PubEq s₁ s₂ := by
  sig_pub [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `pbkdf2` is verified against the shared contract, given the taint checks
and a state satisfying it. -/
theorem verified (hF : FnsOK F) (hc : Checks F) {S : Spec.Hmac.StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2Contract S W Arm.abi 24).pre s) :
    Verified Arm.target F.pbkdf2 (Spec.Pbkdf2.pbkdf2Contract S W Arm.abi 24) := by
  subst hS hW
  refine ⟨fun s hs => WP.mono (correct (hF := hF) (pre_of hF hs) hF.sizes) fun s' ⟨a, h⟩ => ⟨a, ?_⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
      (ct (hF := hF) (pre_of hF h₁) (pre_of hF h₂) (pub_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩
  sig_post [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  exact h

end VG.Proof.Pbkdf2.Whole.Arm
