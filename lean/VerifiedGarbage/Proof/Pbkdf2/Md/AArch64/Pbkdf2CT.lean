import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkLoop

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`, constant time

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Pbkdf2CT.lean`): the pieces between the
calls are checked by the taint analysis (`Checks`, `by taint_decide` for each
hash function), each from registers that the correctness proof fixes to public
values (`KE`, `Mid`, `KR`): they are the same in two runs that agree on the
public arguments. The calls are constant time by their callees' proofs
(`RelCT.call`, with arguments the correctness proof fixes to the same values),
and the branches and the loop go the same way in both runs, by the facts the
correctness proof gives about the registers they test.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK pbkG)
open VG.Proof.Pbkdf2.AArch64 (iterK)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG rel_taint rel_wp)
open VG.Proof.MdStream.AArch64 (wp_lsr wp_subImm)
open Spec.Sha256 (bytesAt)

variable {H : Hash}

/-- The public arguments `entry` reads (`c`, only half public, it only
stores). -/
abbrev entryRegs : List Reg := [.x0, .x1, .x2, .x3, .x5, .x6, .x7]

/-- The taint checks of the pieces of `pbkdf2` between its calls, branches
and loops. -/
structure Checks (H : Hash) : Prop where
  entry : ∃ hc, (Taint.check taint (Taint.ofRegs entryRegs) (.block H.entry) hc).isSome = true
  hk1 : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.hkInit) hc).isSome = true
  hk3 : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.hkUpd) hc).isSome = true
  hk5 : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.hkFin) hc).isSome = true
  hk7 : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.hkKey) hc).isSome = true
  keyShr : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.keyShr) hc).isSome = true
  keySub : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.keySub) hc).isSome = true
  short : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block Hash.short) hc).isSome = true
  su1 : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.initArgs) hc).isSome = true
  su3 : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.saltArgs) hc).isSome = true
  loopRegs : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.loopRegs) hc).isSome = true
  pieceA : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.intArgs) hc).isSome = true
  finArgs : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.finArgs) hc).isSome = true
  pieceC : ∃ hc, (Taint.check taint (Taint.ofRegs epub) (.block H.iterArgs) hc).isSome = true
  tail : ∃ hc, (Taint.check taint (Taint.ofRegs epub)
    (.seq H.outLen (.seq H.outLoop (.block Hash.advance))) hc).isSome = true
  exit : ∃ hc, (Taint.check taint (Taint.ofRegs [.x23]) (.block H.exit) hc).isSome = true

/-- The public arguments are the same (`c` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : (s₀.gpr .x4).setWidth 32 = (s₀'.gpr .x4).setWidth 32
  x5 : s₀.gpr .x5 = s₀'.gpr .x5
  x6 : s₀.gpr .x6 = s₀'.gpr .x6
  x7 : s₀.gpr .x7 = s₀'.gpr .x7
  sp : s₀.sp = s₀'.sp

/-! ## The key's branches, one run at a time -/

section
variable {s₀ : State} (hz : PSizes H)
include hz

theorem keyShr_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.keyShr) s fun t =>
      KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ < H.P.B)) := by
  unfold Hash.keyShr
  exact wp_lsr (log2_B hz).2 fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), key_shr hz h u₁⟩

theorem keySub_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.keySub) s fun t =>
      KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ = H.P.B)) := by
  have hB := hz.B_le
  unfold Hash.keySub
  exact wp_subImm (by omega) fun s₂ u₂ => WP.block_nil ⟨h.upd u₂ (by decide), key_sub h u₂ (by omega)⟩

end

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

/-! ## What agrees in the two runs -/

theorem scr_eq : scr s₀' = scr s₀ := hq.x7.symm
theorem A_eq (o : Nat) : A s₀' o = A s₀ o := by show scr s₀' + _ = scr s₀ + _; rw [scr_eq hq]
theorem pw_eq : pw s₀' = pw s₀ := hq.x0.symm
theorem pwl_eq : pwl s₀' = pwl s₀ := by show (s₀'.gpr .x1).toNat = _; rw [← hq.x1]
theorem salt_eq : salt s₀' = salt s₀ := hq.x2.symm
theorem sl_eq : sl s₀' = sl s₀ := by show (s₀'.gpr .x3).toNat = _; rw [← hq.x3]
theorem cc_eq : cc s₀' = cc s₀ := by show ((s₀'.gpr .x4).setWidth 32).toNat = _; rw [← hq.x4]
theorem out_eq : out s₀' = out s₀ := hq.x5.symm
theorem ol_eq : ol s₀' = ol s₀ := by show (s₀'.gpr .x6).toNat = _; rw [← hq.x6]
theorem nb_eq : nb H s₀' = nb H s₀ := by show (ol s₀' + H.D - 1) / H.D = _; rw [ol_eq hq]
theorem kp_eq : kp H s₀' = kp H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pw s₀' else A s₀' H.hkO) = _; rw [pwl_eq hq, pw_eq hq, A_eq hq]
theorem kl_eq : kl H s₀' = kl H s₀ := by
  show (if pwl s₀' < H.P.B + 1 then pwl s₀' else H.D) = _; rw [pwl_eq hq]

theorem kr_agree {s s' : State} (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ [Reg.x23], s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [h.x23, h'.x23, scr_eq hq]

theorem ke_agree {s s' : State} (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ epub, s.gpr r = s'.gpr r := by
  refine ⟨(kr_agree hq h.kr h'.kr).1, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, pw_eq hq]
  · rw [h.x20, h'.x20, hq.x1]
  · rw [h.x21, h'.x21, salt_eq hq]
  · rw [h.x22, h'.x22, hq.x3]
  · exact (kr_agree hq h.kr h'.kr).2 _ (by simp)

theorem mid_agree {hH : HashOK H} {k : Nat} {s s' : State} (h : Mid hH s₀ k s) (h' : Mid hH s₀' k s') :
    s.sp = s'.sp ∧ ∀ r ∈ epub, s.gpr r = s'.gpr r := by
  refine ⟨(kr_agree hq h.kr h'.kr).1, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19]
  · rw [h.x20, h'.x20, hq.x3]
  · rw [h.x21, h'.x21, ol_eq hq]
  · rw [h.x22, h'.x22, out_eq hq]
  · exact (kr_agree hq h.kr h'.kr).2 _ (by simp)

end

/-! ## The pieces in two runs -/

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Checks H)
include hH hp hp' hz hq hc

omit hH in
theorem entry_rel : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.entry)
    fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s' :=
  rel_taint entryRegs (fun s s' e e' => by
      rw [e, e']
      refine ⟨hq.sp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hq.x0, hq.x1, hq.x2, hq.x3, hq.x5, hq.x6, hq.x7]) hc.entry
    (fun _ e => by rw [e]; exact entry_ok hp hz) (fun _ e => by rw [e]; exact entry_ok hp' hz)

/-- Hashing a password longer than a block. -/
theorem hashKey_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.hashKey
    fun _ _ => True := by
  have hl := layout (H := H); have he := end_le hz
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.hashKey
  have r₁ := rel_taint (G := fun t => KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO)
    (G' := fun t => KE (H := H) s₀' t ∧ t.gpr .x0 = A s₀' H.stWO) epub ag hc.hk1
    (fun _ h => hk1_ok hz h) (fun _ h => hk1_ok hz h)
  have ini : ∀ {σ₀ s : State}, Pre (H := H) σ₀ → KE (H := H) σ₀ s →
      Covers [⟨A σ₀ H.stWO, H.stream.S⟩] s.wr :=
    fun hp h => Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega)
  have c₂ := rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.init_rel hH.stream (st := A s₀ H.stWO)
      (P := fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x0 = A s₀ H.stWO) ∧
        (KE (H := H) s₀' s' ∧ s'.gpr .x0 = A s₀' H.stWO))
      fun s s' h => by
        have i := ini hp h.1.1; have i' := ini hp' h.2.1
        rw [A_eq hq] at i' h
        exact ⟨h.1.2, h.2.2, i, i', (ke_agree hq h.1.1 h.2.1).1⟩)
    (fun _ h => hk2_ok hp hz hH h.1 h.2) (fun _ h => hk2_ok hp' hz hH h.1 h.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [])
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) []) epub
    (fun s s' h h' => ag s s' h.1 h'.1) hc.hk3
    (fun _ h => hk3_ok hp hz hH h.1 h.2) (fun _ h => hk3_ok hp' hz hH h.1 h.2)
  have r₅ := rel_taint
    (F := fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧ hH.SH.Repr t.mem (A s₀' H.stWO) (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk5
    (fun _ h => hk5_ok hp hz hH h.1 h.2) (fun _ h => hk5_ok hp' hz hH h.1 h.2)
  have r₇ := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)))
    (F' := fun t => KE (H := H) s₀' t ∧
      bytesAt t.mem (A s₀' H.hkO) H.D = hH.SH.H.hash (bytesAt s₀'.mem (pw s₀') (pwl s₀')))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.hk7
    (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial) (fun _ h => WP.mono (hk7_ok hz h.1) fun _ _ => trivial)
  refine (r₁.seq (c₂.seq (r₃.seq (RelCT.seq ?_ (r₅.seq (RelCT.seq ?_ r₇)))))).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, pw_eq hq, scr_eq hq, pwl_eq hq] at a'
          exact ⟨a, a', by rw [i, i'], (ke_agree hq k k').1⟩)
        (fun _ h => hk4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.fin_rel hH.stream fun s s' h => by
          obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
          rw [A_eq hq, A_eq hq, scr_eq hq] at a'
          exact ⟨a, a', by rw [i, i', hq.x1], (ke_agree hq k k').1⟩)
        (fun _ h => hk6_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
        (fun _ h => hk6_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The key. -/
theorem key_rel : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.key
    fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .x2 = kp H s₀' ∧ (s'.gpr .x3).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀')) := by
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  obtain ⟨_, hs⟩ := hc.short
  have short : ∀ {P : State → State → Prop}, (∀ s s', P s s' → KE (H := H) s₀ s ∧ KE (H := H) s₀' s') →
      RelCT isa P (.block Hash.short) fun _ _ => True := fun hP =>
    RelCT.taint (A := taint) (Taint.ofRegs epub) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := ke_agree hq (hP _ _ h).1 (hP _ _ h).2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hs
  have ite : RelCT isa (fun s s' => KE (H := H) s₀ s ∧ KE (H := H) s₀' s') H.key fun _ _ => True := by
    unfold Hash.key
    have r₁ := rel_taint
      (G := fun t => KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ < H.P.B)))
      (G' := fun t => KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀' < H.P.B)))
      epub ag hc.keyShr (fun _ h => keyShr_ok hz h) (fun _ h => keyShr_ok hz h)
    refine r₁.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, pwl_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)
    have r₂ := rel_taint
      (F := fun t => KE (H := H) s₀ t) (F' := fun t => KE (H := H) s₀' t)
      (G := fun t => KE (H := H) s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀ = H.P.B)))
      (G' := fun t => KE (H := H) s₀' t ∧ isa.eval (.zero .x .x9) t = some (decide (pwl s₀' = H.P.B)))
      epub ag hc.keySub (fun _ h => keySub_ok hz h) (fun _ h => keySub_ok hz h)
    refine (r₂.seq (RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, pwl_eq hq])
      (short fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
    exact (hashKey_rel hH hp hp' hz hq hc).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  exact (ite.wp fun s s' h => ⟨key_ok hp hz hH h.1, key_ok hp' hz hH h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-- HMAC's states, and the inner one after the salt. -/
theorem setup_rel (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hInd : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => (KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
        KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) ∧
      (KE (H := H) s₀' s' ∧ s'.gpr .x2 = kp H s₀' ∧ (s'.gpr .x3).toNat = kl H s₀' ∧
        KeyAt hH s₀' s'.mem (kp H s₀') (kl H s₀'))) H.setup
      fun s s' => (KE (H := H) s₀ s ∧ States hH s₀ s.mem) ∧ (KE (H := H) s₀' s' ∧ States hH s₀' s'.mem) := by
  have ag := fun (s s' : State) (h : KE (H := H) s₀ s) (h' : KE (H := H) s₀' s') => ke_agree hq h h'
  unfold Hash.setup
  have r₁ := rel_taint
    (F := fun s => KE (H := H) s₀ s ∧ s.gpr .x2 = kp H s₀ ∧ (s.gpr .x3).toNat = kl H s₀ ∧
      KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀))
    (F' := fun s => KE (H := H) s₀' s ∧ s.gpr .x2 = kp H s₀' ∧ (s.gpr .x3).toNat = kl H s₀' ∧
      KeyAt hH s₀' s.mem (kp H s₀') (kl H s₀'))
    (G := fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀))
    (G' := fun t => KE (H := H) s₀' t ∧
      InitArgs (H := H) t (A s₀' H.st0O) (A s₀' H.st1O) (kp H s₀') (scr s₀') (kl H s₀') ∧
      KeyAt hH s₀' t.mem (kp H s₀') (kl H s₀'))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.su1
    (fun _ h => su1_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2) (fun _ h => su1_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2)
  have r₃ := rel_taint (F := fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (Spec.Hmac.xorPad (K0 hH s₀) Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (Spec.Hmac.xorPad (K0 hH s₀) Spec.Hmac.opad))
    (F' := fun t => KE (H := H) s₀' t ∧
      hH.SH.Repr t.mem (A s₀' H.st0O) (Spec.Hmac.xorPad (K0 hH s₀') Spec.Hmac.ipad) ∧
      hH.SH.Repr t.mem (A s₀' H.st1O) (Spec.Hmac.xorPad (K0 hH s₀') Spec.Hmac.opad)) epub
    (fun s s' h h' => ag s s' h.1 h'.1) hc.su3
    (fun _ h => su3_ok hp hz hH h.1 h.2.1 h.2.2) (fun _ h => su3_ok hp' hz hH h.1 h.2.1 h.2.2)
  refine r₁.seq (RelCT.seq ?_ (r₃.seq ?_))
  · exact rel_wp (hinit_rel hH hIn fun s s' h => by
        obtain ⟨⟨k, a, -⟩, ⟨k', a', -⟩⟩ := h
        rw [A_eq hq, A_eq hq, kp_eq hq, scr_eq hq, kl_eq hq] at a'
        exact ⟨a, a', (ke_agree hq k k').1⟩)
      (fun _ h => su2_ok hp hz hH hIn hInd h.1 h.2.1 h.2.2)
      (fun _ h => su2_ok hp' hz hH hIn hInd h.1 h.2.1 h.2.2)
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
        obtain ⟨⟨k, a, i, -⟩, ⟨k', a', i', -⟩⟩ := h
        rw [A_eq hq, salt_eq hq, scr_eq hq, sl_eq hq] at a'
        exact ⟨a, a', by rw [i, i'], (ke_agree hq k k').1⟩)
      (fun _ h => su4_ok hp hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      (fun _ h => su4_ok hp' hz hH h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)

end

/-! ## The blocks of the output -/

theorem inv_mid {hH : HashOK H} {s₀ : State} (hz : PSizes H) {k : Nat} (hk : k < nb H s₀) {s : State}
    (h : Inv hH s₀ k s) : Mid hH s₀ k s := by
  have hkD : k * H.D < ol s₀ := (lt_nb hz.z.D0).1 hk
  have hd : done H s₀ k = k * H.D := by show min _ _ = _; omega
  have hb := h.outB
  rw [hd, List.take_of_length_le (Nat.le_of_eq h.glen)] at hb
  exact ⟨h.kr, h.st, h.x19, h.x20, by rw [h.x21, hd], by rw [h.x22, hd], hb⟩

/-- The loop's invariant in two runs, with `n` blocks left. -/
abbrev LI (hH : HashOK H) (s₀ s₀' : State) (n : Nat) (s s' : State) : Prop :=
  n ≤ nb H s₀ ∧ 0 < n ∧ Inv hH s₀ (nb H s₀ - n) s ∧ Inv hH s₀' (nb H s₀ - n) s'

section
variable (hH : HashOK H) {s₀ s₀' : State} (hp : Pre (H := H) s₀) (hp' : Pre (H := H) s₀') (hz : PSizes H)
  (hq : PubEq s₀ s₀') (hc : Checks H)
  (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) (hFd : H.hmacFin.aarch64Depth ≤ 1)
  (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hId : H.iterate.aarch64Depth ≤ 1)
include hH hp hp' hz hq hc hF hFd hI hId

theorem block_mid_rel {k : Nat} (hk : k < nb H s₀) (hg : (G hH s₀ k).length = k * H.D)
    (hg' : (G hH s₀' k).length = k * H.D) :
    RelCT isa (fun s s' => Mid hH s₀ k s ∧ Mid hH s₀' k s') H.block fun _ _ => True := by
  have hk' : k < nb H s₀' := by rw [nb_eq hq]; exact hk
  have ag := fun (s s' : State) (h : Mid hH s₀ k s) (h' : Mid hH s₀' k s') => mid_agree hq h h'
  have msp : ∀ {s s' : State}, Mid hH s₀ k s → Mid hH s₀' k s' → s.sp = s'.sp :=
    fun h h' => (mid_agree hq h h').1
  unfold Hash.block
  have pA := rel_taint epub ag hc.pieceA (fun _ h => pieceA_ok hp hz hH hk h)
    (fun _ h => pieceA_ok hp' hz hH hk' h)
  have fA := rel_taint
    (F := fun t => Mid hH s₀ k t ∧ hH.SH.Repr t.mem (A s₀ H.stWO)
      (Spec.Hmac.xorPad (K0 hH s₀) Spec.Hmac.ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (F' := fun t => Mid hH s₀' k t ∧ hH.SH.Repr t.mem (A s₀' H.stWO)
      (Spec.Hmac.xorPad (K0 hH s₀') Spec.Hmac.ipad ++ saltB s₀' ++ Spec.Pbkdf2.int (k + 1)))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.finArgs
    (fun _ h => finArgs_ok hp hz hH h.1 h.2) (fun _ h => finArgs_ok hp' hz hH h.1 h.2)
  have pC := rel_taint
    (F := fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.uO) H.D = U1 hH s₀ k)
    (F' := fun t => Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.uO) H.D = U1 hH s₀' k)
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.pieceC
    (fun _ h => pieceC_ok hp hz hH hk h.1 h.2) (fun _ h => pieceC_ok hp' hz hH hk' h.1 h.2)
  have tl := rel_taint (G := fun _ => True) (G' := fun _ => True)
    (F := fun t => Mid hH s₀ k t ∧ bytesAt t.mem (A s₀ H.tO) H.D = Tb hH s₀ (k + 1))
    (F' := fun t => Mid hH s₀' k t ∧ bytesAt t.mem (A s₀' H.tO) H.D = Tb hH s₀' (k + 1))
    epub (fun s s' h h' => ag s s' h.1 h'.1) hc.tail
    (fun _ h => WP.mono (tail_ok hp hz hH hk hg h.1 h.2) fun _ _ => trivial)
    (fun _ h => WP.mono (tail_ok hp' hz hH hk' hg' h.1 h.2) fun _ _ => trivial)
  refine (pA.seq (RelCT.seq ?_ (fA.seq (RelCT.seq ?_ (pC.seq (RelCT.seq ?_ tl)))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · exact rel_wp (VG.Proof.Pbkdf2.Md.AArch64.Calls.upd_rel hH.stream fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [A_eq hq, A_eq hq, scr_eq hq] at x
        exact ⟨a.args, x, by rw [a.x1, a'.x1, sl_eq hq], msp a.mid a'.mid⟩)
      (fun _ h => callA_ok hp hz hH hk h) (fun _ h => callA_ok hp' hz hH hk' h)
  · exact rel_wp (hfin_rel hH hF fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [A_eq hq, A_eq hq, A_eq hq, ← hq.x3, scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => callB_ok hp hz hH hF hFd hk h) (fun _ h => callB_ok hp' hz hH hF hFd hk' h)
  · exact rel_wp (iter_rel hH hI fun s s' h => by
        obtain ⟨a, a'⟩ := h
        have x := a'.args
        rw [A_eq hq, A_eq hq, A_eq hq, cc_eq hq, scr_eq hq] at x
        exact ⟨a.args, x, msp a.mid a'.mid⟩)
      (fun _ h => callC_ok hp hz hH hI hId hk h) (fun _ h => callC_ok hp' hz hH hI hId hk' h)

theorem block_rel {k : Nat} (hk : k < nb H s₀) :
    RelCT isa (fun s s' => Inv hH s₀ k s ∧ Inv hH s₀' k s') H.block fun s s' =>
      (Inv hH s₀ (k + 1) s ∧ isa.eval (.nonzero .x .x21) s = some (decide (k + 1 ≠ nb H s₀))) ∧
      (Inv hH s₀' (k + 1) s' ∧ isa.eval (.nonzero .x .x21) s' = some (decide (k + 1 ≠ nb H s₀'))) := by
  have hk' : k < nb H s₀' := by rw [nb_eq hq]; exact hk
  intro s₁ s₂ t₁ t₂ s₁' s₂' h e₁ e₂
  refine ((((block_mid_rel hH hp hp' hz hq hc hF hFd hI hId hk h.1.glen h.2.glen).mono
    (P' := fun s s' => Inv hH s₀ k s ∧ Inv hH s₀' k s') (fun _ _ h => ⟨inv_mid hz hk h.1, inv_mid hz hk' h.2⟩)
    fun _ _ h => h).wp fun s s' h => ⟨block_ok hp hz hH hF hFd hI hId hk h.1,
      block_ok hp' hz hH hF hFd hI hId hk' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2)
    _ _ _ _ _ _ h e₁ e₂

theorem step_rel (n : Nat) :
    RelCT isa (LI hH s₀ s₀' n) H.block fun s s' =>
      isa.eval (.nonzero .x .x21) s = isa.eval (.nonzero .x .x21) s' ∧
      (isa.eval (.nonzero .x .x21) s = some false → Inv hH s₀ (nb H s₀) s ∧ Inv hH s₀' (nb H s₀') s') ∧
      (isa.eval (.nonzero .x .x21) s = some true → ∃ m < n, LI hH s₀ s₀' m s s') := by
  by_cases hn : n ≤ nb H s₀ ∧ 0 < n
  · have hk : nb H s₀ - n < nb H s₀ := by omega
    refine ((block_rel hH hp hp' hz hq hc hF hFd hI hId hk).mono (P' := LI hH s₀ s₀' n)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩) fun _ _ h => h).mono (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e := nb_eq (H := H) hq
    rw [z, z', e]
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
    RelCT isa (fun s s' => (Inv hH s₀ 0 s ∧ isa.eval (.zero .x .x21) s = some (decide (ol s₀ = 0))) ∧
        (Inv hH s₀' 0 s' ∧ isa.eval (.zero .x .x21) s' = some (decide (ol s₀' = 0))))
      (.ite (.zero .x .x21) (.block []) (.loop H.block (.nonzero .x .x21)))
      fun s s' => Inv hH s₀ (nb H s₀) s ∧ Inv hH s₀' (nb H s₀') s' := by
  have hD := hz.z.D0
  have e := nb_eq (H := H) hq; have eo := ol_eq hq
  refine RelCT.ite (fun s s' h => by rw [h.1.2, h.2.2, eo]) ?_ ?_
  · refine RelCT.block_nil fun s s' h => ?_
    have h0 : ol s₀ = 0 := by have := h.1.1.2.symm.trans h.2; simpa using this
    rw [e, (nb_zero hD).2 h0]
    exact ⟨h.1.1.1, h.1.2.1⟩
  · refine (RelCT.loop (M := isa) (LI hH s₀ s₀') (step_rel hH hp hp' hz hq hc hF hFd hI hId)
      (nb H s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have h0 : ol s₀ ≠ 0 := by have := h.1.1.2.symm.trans h.2; simpa using this
    have : nb H s₀ ≠ 0 := fun x => h0 ((nb_zero hD).1 x)
    refine ⟨Nat.le_refl _, Nat.pos_of_ne_zero this, ?_, ?_⟩ <;> rw [Nat.sub_self]
    exacts [h.1.1.1, h.1.2.1]

theorem ct (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hInd : H.hmacInit.aarch64Depth ≤ 1) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.pbkdf2 fun _ _ => True := by
  unfold Hash.pbkdf2
  have lr := rel_taint (F := fun s => KE (H := H) s₀ s ∧ States hH s₀ s.mem)
    (F' := fun s => KE (H := H) s₀' s ∧ States hH s₀' s.mem)
    (G := fun t => Inv hH s₀ 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀ = 0)))
    (G' := fun t => Inv hH s₀' 0 t ∧ isa.eval (.zero .x .x21) t = some (decide (ol s₀' = 0)))
    epub (fun s s' h h' => ke_agree hq h.1 h'.1) hc.loopRegs
    (fun _ h => loopRegs_ok hp hz hH h.1 h.2) (fun _ h => loopRegs_ok hp' hz hH h.1 h.2)
  obtain ⟨_, hx⟩ := hc.exit
  have ex : RelCT isa (fun s s' => Inv hH s₀ (nb H s₀) s ∧ Inv hH s₀' (nb H s₀') s') (.block H.exit)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x23]) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1.kr h.2.kr
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hx
  exact (entry_rel hp hp' hz hq hc).seq ((key_rel hH hp hp' hz hq hc).seq
    ((setup_rel hH hp hp' hz hq hc hIn hInd).seq
      (lr.seq ((loop_rel hH hp hp' hz hq hc hF hFd hI hId).seq ex))))

end

/-- `pbkdf2` is verified against `pbkG`, given the taint checks and the
proofs of the functions it calls. -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H)
    (hIn : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hInd : H.hmacInit.aarch64Depth ≤ 1)
    (hF : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) (hFd : H.hmacFin.aarch64Depth ≤ 1)
    (hI : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hId : H.iterate.aarch64Depth ≤ 1)
    (hsat : ∃ s, (pbkG hH.SH (H.W + H.S)).pre s) :
    Verified AArch64.target H.pbkdf2 (pbkG hH.SH (H.W + H.S)) := by
  refine ⟨fun s hs => correct (pre_of hH hs) hH.psizes hH hIn hInd hF hFd hI hId,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
  exact (ct hH (pre_of hH h₁) (pre_of hH h₂) hH.psizes ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hc hF hFd hI hId
    hIn hInd _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.Pbk
