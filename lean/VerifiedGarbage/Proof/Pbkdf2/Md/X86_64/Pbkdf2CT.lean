import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkLoop

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`, constant time

The pieces between the calls are checked by the taint analysis (`Checks`, `by
taint_decide` for each hash function), each from registers that the
correctness proof fixes to public values (`KE`, `Mid`, `KR`): they are the
same in two runs that agree on the public arguments. The calls are constant
time by their callees' proofs (`RelCT.call`, with arguments the correctness
proof fixes to the same values), and the branches and the loop go the same way
in both runs, by the facts the correctness proof gives about their flags.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK pbkG pbkImp)
open VG.Proof.Pbkdf2.X86_64 (iterK)
open VG.Proof.Hmac.Generic.X86_64 (initG finG rel_taint rel_wp)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-- The taint checks of the pieces of `pbkdf2` between its calls, branches
and loops. -/
structure Checks (H : Hash) : Prop where
  load : ∃ hc, (Taint.check taint (Taint.ofRegs [.rsp]) (.block Hash.loadScr) hc).isSome = true
  entry : ∃ hc, (Taint.check taint (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (.block H.entry) hc).isSome = true
  hk1 : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO)) hc).isSome = true
  hk3 : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx),
      .mov .rcx (.reg .rbp), .mov .r8 (.reg .r15)] : List Instr))) hc).isSome = true
  hk5 : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stWO ++ ([.mov .rsi (.reg .rbp)] : List Instr) ++
      VG.Impl.Hmac.Generic.X86_64.scr .rdx H.hkO ++ ([.mov .rcx (.reg .r15)] : List Instr))) hc).isSome = true
  hk7 : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdx H.hkO ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr))) hc).isSome = true
  short : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.block [.mov .rdx (.reg .rbx), .mov .rcx (.reg .rbp)]) hc).isSome = true
  su1 : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.st0O ++ VG.Impl.Hmac.Generic.X86_64.scr .rsi H.st1O ++
      ([.mov .r8 (.reg .r15)] : List Instr))) hc).isSome = true
  su3 : ∃ hc, (Taint.check taint (Taint.ofRegs eregs)
    (.seq (VG.Impl.Hmac.Generic.X86_64.copy .r15 H.st0O .r15 H.stSO H.S)
      (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.stSO ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)),
        .mov .rdx (.reg .r12), .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)))) hc).isSome = true
  loopRegs : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.loopRegs) hc).isSome = true
  pieceA : ∃ hc, (Taint.check taint (Taint.ofRegs mregs)
    (.seq (VG.Impl.Hmac.Generic.X86_64.copy .r15 H.stSO .r15 H.stWO H.S) (.block H.intArgs)) hc).isSome = true
  finArgs : ∃ hc, (Taint.check taint (Taint.ofRegs mregs) (.block H.finArgs) hc).isSome = true
  pieceC : ∃ hc, (Taint.check taint (Taint.ofRegs mregs)
    (.seq (VG.Impl.Hmac.Generic.X86_64.copy .r15 H.uO .r15 H.tO H.D) (.block H.iterArgs)) hc).isSome = true
  tail : ∃ hc, (Taint.check taint (Taint.ofRegs mregs)
    (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) hc).isSome = true
  exit : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.exit) hc).isSome = true

/-- The public arguments are the same (`c` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : (s₀.gpr .r8).setWidth 32 = (s₀'.gpr .r8).setWidth 32
  r9 : s₀.gpr .r9 = s₀'.gpr .r9
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

/-! ## What agrees in the two runs -/

theorem scr_eq : scr s₀' = scr s₀ := hq.a1.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show scr s₀' + _ = scr s₀ + _; rw [scr_eq hq]
theorem pw_eq : pw s₀' = pw s₀ := hq.rdi.symm
theorem pwl_eq : pwl s₀' = pwl s₀ := by show (s₀'.gpr .rsi).toNat = _; rw [← hq.rsi]
theorem salt_eq : salt s₀' = salt s₀ := hq.rdx.symm
theorem sl_eq : sl s₀' = sl s₀ := by show (s₀'.gpr .rcx).toNat = _; rw [← hq.rcx]
theorem cc_eq : cc s₀' = cc s₀ := by show ((s₀'.gpr .r8).setWidth 32).toNat = _; rw [← hq.r8]
theorem out_eq : out s₀' = out s₀ := hq.r9.symm
theorem ol_eq : ol s₀' = ol s₀ := by show (stackArg s₀' 0).toNat = _; rw [← hq.a0]
theorem nb_eq : nb H s₀' = nb H s₀ := by show (ol s₀' + H.D - 1) / H.D = _; rw [ol_eq hq]
theorem kp_eq : kp H s₀' = kp H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pw s₀' else A s₀' H.hkO) = _; rw [pwl_eq hq, pw_eq hq, A_eq hq]
theorem kl_eq : kl H s₀' = kl H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pwl s₀' else H.D) = _; rw [pwl_eq hq]

theorem kr_agree {s s' : State} (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.r15, h'.r15, scr_eq hq]
  · rw [h.rsp, h'.rsp, hq.rsp]

theorem ke_agree {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') :
    ∀ r ∈ eregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, pw_eq hq]
  · rw [h.rbp, h'.rbp, hq.rsi]
  · rw [h.r12, h'.r12, salt_eq hq]
  · rw [h.r13, h'.r13, hq.rcx]
  · exact kr_agree hq h.kr h'.kr _ (by simp)
  · exact kr_agree hq h.kr h'.kr _ (by simp)

theorem mid_agree {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) (h' : Mid hH s₀' k s') :
    ∀ r ∈ mregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]
  · rw [h.rbp, h'.rbp, hq.rcx]
  · rw [h.r12, h'.r12, ol_eq hq]
  · rw [h.r13, h'.r13, out_eq hq]
  · exact kr_agree hq h.kr h'.kr _ (by simp)
  · exact kr_agree hq h.kr h'.kr _ (by simp)

theorem ke_rsp {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') : s.gpr .rsp = s'.gpr .rsp :=
  ke_agree hq h h' _ (by simp)

end

/-! ## The pieces in two runs -/

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Checks H)
include hH hp hp' hz hq hc

omit hH in
/-- The entry, up to the comparison of the password's length. -/
theorem entry_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.seq (.block Hash.loadScr) (.block H.entry))
    fun s s' => (KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1))) ∧
      (KE (H := H) s₀' s' ∧ s'.cf = some (decide (pwl s₀' < H.P.B + 1))) := by
  have l := rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := Loaded s₀) (G' := Loaded s₀') [.rsp]
    (fun s s' e e' r hr => by
      rw [e, e']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hq.rsp) hc.load
    (fun _ e => by rw [e]; exact loadScr_ok hp) (fun _ e => by rw [e]; exact loadScr_ok hp')
  have e := rel_taint (F := Loaded s₀) (F' := Loaded s₀')
    (G := fun s => KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1)))
    (G' := fun s => KE (H := H) s₀' s ∧ s.cf = some (decide (pwl s₀' < H.P.B + 1)))
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (fun s s' l l' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rdi]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rsi]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rdx]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rcx]
      · rw [l.r8, l'.r8, scr_eq hq]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.r9]
      · rw [l.other _ (by decide) (by decide), l'.other _ (by decide) (by decide), hq.rsp]) hc.entry
    (fun _ l => WP.mono (entry_ok hp hz l) fun _ ⟨k, a, b, c, d, f⟩ => ⟨⟨k, a, b, c, d⟩, f⟩)
    (fun _ l => WP.mono (entry_ok hp' hz l) fun _ ⟨k, a, b, c, d, f⟩ => ⟨⟨k, a, b, c, d⟩, f⟩)
  exact l.seq e

/-- Hashing a password longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hB := hz.z.B_le; have hN := hz.z.N; have hD := hz.z.D
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => KE (H := H) s₀ t ∧ t.gpr .rdi = A s₀ H.stWO)
    (G' := fun t => KE (H := H) s₀' t ∧ t.gpr .rdi = A s₀' H.stWO) eregs ag hc.hk1
    (fun _ h => hk1_ok hz h) (fun _ h => hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, Pre (H := H) σ₀ → KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.S⟩] s.wr ∧ (below (s.gpr .rsp) 16).Disjoint ⟨A σ₀ H.stWO, H.S⟩ :=
    fun hp h => ⟨Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega),
      stk_sc hp h.kr (by omega) (part_sub (by omega))⟩
  have c₂ := rel_wp (VG.Proof.Hmac.Generic.X86_64.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (KE (H := H) s₀ s ∧ s.gpr .rdi = A s₀ H.stWO) ∧
        (KE (H := H) s₀' s' ∧ s'.gpr .rdi = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i.1, i'.1, i.2, i'.2, ke_rsp hq h.1.1 h.2.1⟩)
    (fun _ h => hk2_ok hp hz hH h.1 h.2) (fun _ h => hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) eregs
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => hk3_ok hp hz hH h.1 h.2) (fun _ h => hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => hk5_ok hp hz hH h.1 h.2) (fun _ h => hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => KE (H := H) s₀ t ∧ bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h) fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Hmac.Generic.X86_64.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, pw_eq hq, scr_eq hq, pwl_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], ke_rsp hq k k'⟩)
        (fun _ h => hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Hmac.Generic.X86_64.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, A_eq hq, scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.rsi], ke_rsp hq k k'⟩)
        (fun _ h => hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1))) ∧
      (KE (H := H) s₀' s' ∧ s'.cf = some (decide (pwl s₀' < H.P.B + 1)))) H.key
    fun s s' => (KE (H := H) s₀ s ∧ s.gpr .rdx = kp H s₀ ∧ (s.gpr .rcx).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .rdx = kp H s₀' ∧ (s'.gpr .rcx).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')) := by
  have ite : RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.cf = some (decide (pwl s₀ < H.P.B + 1))) ∧
      (KE (H := H) s₀' s' ∧ s'.cf = some (decide (pwl s₀' < H.P.B + 1)))) H.key fun _ _ => True := by
    unfold Hash.key
    refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, pwl_eq hq]) ?_ ?_
    · exact (hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    · obtain ⟨_, hs⟩ := hc.short
      exact RelCT.taint (A := taint) (Taint.ofRegs eregs)
        (fun _ _ h => Taint.agree_ofRegs (ke_agree hq h.1.1.1 h.1.2.1)) hs
  exact (ite.wp fun s s' h => ⟨key_ok hp hz hH h.1.1 h.1.2, key_ok hp' hz hH h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- HMAC's states, and the inner one after the salt. -/
theorem setup_rel (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hInsp : NoSp H.hmacInit)
    (hInd : H.hmacInit.depth ≤ 2) :
    RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.gpr .rdx = kp H s₀ ∧ (s.gpr .rcx).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .rdx = kp H s₀' ∧ (s'.gpr .rcx).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀'))) H.setup
      fun s s' => (KE (H := H) s₀ s ∧ States hH s₀ s.mem) ∧ (KE (H := H) s₀' s' ∧ States hH s₀' s'.mem) := by
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.setup
  have r₁ := rel_taint
    (F := fun s => KE (H := H) s₀ s ∧ s.gpr .rdx = kp H s₀ ∧ (s.gpr .rcx).toNat = kl H s₀ ∧
      KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀))
    (F' := fun s => KE (H := H) s₀' s ∧ s.gpr .rdx = kp H s₀' ∧ (s.gpr .rcx).toNat = kl H s₀' ∧
      KeyAt hH s₀' s.mem (kp H s₀') (kl H s₀'))
    (G := fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀))
    (G' := fun t => KE (H := H) s₀' t ∧
      InitArgs (H := H) t (A s₀' H.st0O) (A s₀' H.st1O) (kp H s₀') (scr s₀') (kl H s₀') ∧
      KeyAt hH s₀' t.mem (kp H s₀') (kl H s₀'))
    eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.su1
    (fun _ h => su1_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => su1_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (Spec.Hmac.xorPad (K0 hH s₀) Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (Spec.Hmac.xorPad (K0 hH s₀) Spec.Hmac.opad))
    (F' := fun t => KE (H := H) s₀' t ∧
      hH.SH.Repr t.mem (A s₀' H.st0O) (Spec.Hmac.xorPad (K0 hH s₀') Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀' H.st1O) (Spec.Hmac.xorPad (K0 hH s₀') Spec.Hmac.opad)) eregs (fun s s' h h' => ag s s' h.1 h'.1) hc.su3
    (fun _ h => su3_ok hp hz hH h.1 h.2.1 h.2.2) (fun _ h => su3_ok hp' hz hH h.1 h.2.1 h.2.2)
  refine r₁.seq (RelCT.seq ?_ (RelCT.assoc (r₃.seq ?_)))
  · exact rel_wp (hinit_rel hH hIn fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [A_eq hq, A_eq hq, kp_eq hq, scr_eq hq, kl_eq hq] at a'
        exact ⟨a, a', ke_rsp hq k k'⟩)
      (fun _ h => su2_ok hp hz hH hIn hInsp hInd h.1 h.2.1 h.2.2)
      (fun _ h => su2_ok hp' hz hH hIn hInsp hInd h.1 h.2.1 h.2.2)
  · exact rel_wp (VG.Proof.Hmac.Generic.X86_64.upd_rel hH.stream fun s s' h => by
        obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
        rw [A_eq hq, salt_eq hq, scr_eq hq, sl_eq hq] at a'
        exact ⟨a, a', by rw [i, i'], ke_rsp hq k k'⟩)
      (fun _ h => su4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      (fun _ h => su4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)

end

/-! ## The blocks of the output -/

theorem inv_mid {hH : HashOK H} {s₀ : State} (hz : PSizes H) {k : Nat} (hk : k < nb H s₀) {s : State}
    (h : Inv hH s₀ k s) : Mid hH s₀ k s := by
  have hkD : k * H.D < ol s₀ := (lt_nb hz.z.D.1).1 hk
  have hd : done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  exact ⟨h.kr, h.st, h.rbx, h.rbp, by rw [h.r12, hd], by rw [h.r13, hd], hb⟩

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LI (hH : HashOK H) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  n ≤ nb H s₀ ∧ 0 < n ∧ Inv hH s₀ (nb H s₀ - n) s ∧ Inv hH s₀' (nb H s₀ - n) s'

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Checks H)
  (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
  (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
include hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId

theorem block_mid_rel {k : Nat} (hk : k < nb H s₀) (hg : (G hH s₀ k).length = k * H.D)
    (hg' : (G hH s₀' k).length = k * H.D) :
    RelCT isa (fun s s' => Mid hH s₀ k s ∧ Mid hH s₀' k s') H.block fun _ _ => True := by
  have hk' : k < nb H s₀' := by rw [nb_eq hq]; exact hk
  have ag := fun (s s' : State) (h : Mid hH s₀ k s) (h' : Mid hH s₀' k s') => mid_agree hq h h'
  have msp : ∀ {s s' : State}, Mid hH s₀ k s → Mid hH s₀' k s' → s.gpr .rsp = s'.gpr .rsp :=
    fun h h' => mid_agree hq h h' _ (by simp)
  unfold Hash.block
  have pA := rel_taint mregs ag hc.pieceA (fun _ h => pieceA_ok hp hz hH hk h) (fun _ h => pieceA_ok hp' hz hH hk' h)
  have fA := rel_taint
    (F := fun t => Mid hH s₀ k t ∧ hH.SH.Repr t.mem (A s₀ H.stWO)
      (Spec.Hmac.xorPad (K0 hH s₀) Spec.Hmac.ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (F' := fun t => Mid hH s₀' k t ∧ hH.SH.Repr t.mem (A s₀' H.stWO)
      (Spec.Hmac.xorPad (K0 hH s₀') Spec.Hmac.ipad ++ saltB s₀' ++ Spec.Pbkdf2.int (k + 1)))
    mregs (fun s s' h h' => ag s s' h.1 h'.1) hc.finArgs
    (fun _ h => finArgs_ok hp hz hH hk h.1 h.2) (fun _ h => finArgs_ok hp' hz hH hk' h.1 h.2)
  have pC := rel_taint
    (F := fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = U1 hH s₀ k)
    (F' := fun t => Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.uO) H.D = U1 hH s₀' k)
    mregs (fun s s' h h' => ag s s' h.1 h'.1) hc.pieceC
    (fun _ h => pieceC_ok hp hz hH hk h.1 h.2) (fun _ h => pieceC_ok hp' hz hH hk' h.1 h.2)
  have tl := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1))
    (F' := fun t => Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.tO) H.D = Tb hH s₀' (k + 1))
    mregs (fun s s' h h' => ag s s' h.1 h'.1) hc.tail
    (fun _ h => WP.mono (tail_ok hp hz hH hk hg h.1 h.2) fun _ _ => trivial)
    (fun _ h => WP.mono (tail_ok hp' hz hH hk' hg' h.1 h.2) fun _ _ => trivial)
  refine (RelCT.assoc (pA.seq (RelCT.seq ?_ (fA.seq (RelCT.seq ?_ (RelCT.assoc (pC.seq (RelCT.seq ?_ tl)))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Hmac.Generic.X86_64.upd_rel hH.stream fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [A_eq hq, A_eq hq, scr_eq hq] at x
        exact ⟨a.args, x, by rw [a.rsi, a'.rsi, hq.rcx], msp a.mid a'.mid⟩)
      (fun _ h => callA_ok hp hz hH hk h) (fun _ h => callA_ok hp' hz hH hk' h)
  · exact rel_wp (hfin_rel hH hF fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [A_eq hq, A_eq hq, A_eq hq, ← hq.rcx, scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => callB_ok hp hz hH hF hFsp hFd hk h) (fun _ h => callB_ok hp' hz hH hF hFsp hFd hk' h)
  · exact rel_wp (iter_rel hH hI fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [A_eq hq, A_eq hq, A_eq hq, cc_eq hq, scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => callC_ok hp hz hH hI hIsp hId hk h) (fun _ h => callC_ok hp' hz hH hI hIsp hId hk' h)

theorem block_rel {k : Nat} (hk : k < nb H s₀) :
    RelCT isa (fun s s' => Inv hH s₀ k s ∧ Inv hH s₀' k s') H.block fun s s' =>
      (Inv hH s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = nb H s₀))) ∧
      (Inv hH s₀' (k + 1) s' ∧ s'.zf = some (decide (k + 1 = nb H s₀'))) := by
  have hk' : k < nb H s₀' := by rw [nb_eq hq]; exact hk
  intro s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂
  refine ((((block_mid_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId hk h.1.glen h.2.glen).mono
    (P' := fun s s' => Inv hH s₀ k s ∧ Inv hH s₀' k s') (fun _ _ h => ⟨inv_mid hz hk h.1, inv_mid hz hk' h.2⟩)
    fun _ _ h => h).wp fun s s' h => ⟨block_ok hp hz hH hF hFsp hFd hI hIsp hId hk h.1,
      block_ok hp' hz hH hF hFsp hFd hI hIsp hId hk' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2)
    _ _ _ _ _ _ h e₁ e₂

theorem step_rel (n : Nat) :
    RelCT isa (LI hH s₀ s₀' n) H.block fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → Inv hH s₀ (nb H s₀) s ∧ Inv hH s₀' (nb H s₀') s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LI hH s₀ s₀' m s s') := by
  by_cases hn : n ≤ nb H s₀ ∧ 0 < n
  · have hk : nb H s₀ - n < nb H s₀ := by omega
    refine ((block_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId hk).mono (P' := LI hH s₀ s₀' n)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e := nb_eq (H := H) hq
    have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
    rw [ev, ev, z, z', e]
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : nb H s₀ - n + 1 = nb H s₀ := by simpa using hf
      rw [hl] at i i'
      exact ⟨i, i'⟩
    · have hl : nb H s₀ - n + 1 ≠ nb H s₀ := by simpa using ht
      have e' : nb H s₀ - (n - 1) = nb H s₀ - n + 1 := by omega
      exact ⟨n - 1, by omega, by omega, by omega, e' ▸ i, e' ▸ i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel :
    RelCT isa (fun s s' => (Inv hH s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0))) ∧
        (Inv hH s₀' 0 s' ∧ s'.zf = some (decide (ol s₀' = 0))))
      (.ite .e (.block []) (.loop H.block .ne)) fun s s' => Inv hH s₀ (nb H s₀) s ∧ Inv hH s₀' (nb H s₀') s' := by
  have hD := hz.z.D.1
  have e := nb_eq (H := H) hq; have eo := ol_eq hq
  refine RelCT.ite (fun s s' h => by simp [eval, h.1.2, h.2.2, eo]) ?_ ?_
  · refine RelCT.block_nil fun s s' h => ?_
    have h0 : ol s₀ = 0 := by simpa [eval, h.1.1.2] using h.2
    rw [e, (nb_zero hD).2 h0]
    exact ⟨h.1.1.1, h.1.2.1⟩
  · refine (RelCT.loop (M := isa) (LI hH s₀ s₀') (step_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId)
      (nb H s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have h0 : ol s₀ ≠ 0 := by simpa [eval, h.1.1.2] using h.2
    have : nb H s₀ ≠ 0 := fun x => h0 ((nb_zero hD).1 x)
    refine ⟨Nat.le_refl _, Nat.pos_of_ne_zero this, ?_, ?_⟩ <;> rw [Nat.sub_self]
    exacts [h.1.1.1, h.1.2.1]

theorem ct (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hInsp : NoSp H.hmacInit)
    (hInd : H.hmacInit.depth ≤ 2) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.pbkdf2 fun _ _ => True := by
  unfold Hash.pbkdf2
  have lr := rel_taint (F := fun s => KE (H := H) s₀ s ∧ States hH s₀ s.mem)
    (F' := fun s => KE (H := H) s₀' s ∧ States hH s₀' s.mem)
    (G := fun t => Inv hH s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)))
    (G' := fun t => Inv hH s₀' 0 t ∧ t.zf = some (decide (ol s₀' = 0)))
    kregs (fun s s' h h' => kr_agree hq h.1.kr h'.1.kr) hc.loopRegs
    (fun _ h => loopRegs_ok hp hz hH h.1.kr h.1.r13 h.2) (fun _ h => loopRegs_ok hp' hz hH h.1.kr h.1.r13 h.2)
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => Inv hH s₀ (nb H s₀) s ∧ Inv hH s₀' (nb H s₀') s') (.block H.exit)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1.kr h.2.kr)) hx
  exact RelCT.assoc ((entry_rel hp hp' hz hq hc).seq ((key_rel hH hp hp' hz hq hc).seq
    ((setup_rel hH hp hp' hz hq hc hIn hInsp hInd).seq
      (lr.seq ((loop_rel hH hp hp' hz hq hc hF hFsp hFd hI hIsp hId).seq ex)))))

end

/-- `pbkdf2` is verified against `pbkG`, given the taint checks, the proofs
of the functions it calls, and the facts about its code that the kernel
checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) (hz : PSizes H) (hc : Checks H)
    (hIn : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hInsp : NoSp H.hmacInit)
    (hInd : H.hmacInit.depth ≤ 2)
    (hF : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) (hFsp : NoSp H.hmacFin) (hFd : H.hmacFin.depth ≤ 2)
    (hI : Verified X86_64.target H.iterate (iterK hH.SH H.W)) (hIsp : NoSp H.iterate) (hId : H.iterate.depth ≤ 2)
    (hmx : H.pbkdf2.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (pbkG hH.SH (H.W + H.S)).pre s) :
    Verified X86_64.target H.pbkdf2 (pbkG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct (pre_of hH hs) hz hH hIn hInsp hInd hF hFsp hFd hI hIsp hId
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
    exact (ct hH (pre_of hH h₁) (pre_of hH h₂) hz ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hc hF hFsp hFd hI hIsp
      hId hIn hInsp hInd _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
