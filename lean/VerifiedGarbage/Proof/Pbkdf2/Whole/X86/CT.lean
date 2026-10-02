import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: constant time

As for `iterate` (`Proof/Pbkdf2/Generic/X86/IterateCT.lean`): the pieces of
code between the calls are checked by the taint analysis (`Checks`, which the
kernel evaluates for each hash function), with the arguments, `esp`, `ebp`
and, in the loop over the blocks, `ebx` public (`piece`); the calls are
related by their contracts (`init_rel`, `upd_rel`, `fin_rel`, `hi_rel`,
`hf_rel`, `it_rel`), whose public arguments are the same in two runs with the
same public arguments (`PubEq`). The branches (whether the password is hashed,
and the loop over the blocks) depend only on the lengths.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Hmac.Generic.X86 (Hash at_ copy)
open VG.Proof.Hmac.Generic.X86 (HashOK argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel upd_rel fin_rel)
open VG.Proof.Sha256.X86.Stream (eval_e eval_ne)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the arguments and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs (4 + 4 * 8)) c hc).isSome = true

/-- The taint checks of the pieces of `pbkdf2` between its calls. -/
structure Checks (F : Fns) : Prop where
  pro : Ck [] (.block F.prologue)
  cmp : Ck [.ebp] (.block F.cmpPw)
  hk1 : Ck [.ebp] (.block (VG.Impl.Hmac.Generic.X86.scr .edi F.stWO))
  hk3 : Ck [.ebp] (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (Fns.argM 1), .mov .edx (Fns.argM 0)])
  hk5 : Ck [.ebp] (.block ([.mov .eax (Fns.argM 1), .mov .ecx (.imm 0)] ++ VG.Impl.Hmac.Generic.X86.scr .edx F.hkO))
  hk7 : Ck [.ebp]
    (.block (VG.Impl.Hmac.Generic.X86.scr .edx F.hkO ++ [.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))]))
  short : Ck [.ebp] (.block [.mov .edx (Fns.argM 0)])
  su1 : Ck [.ebp] (.block (VG.Impl.Hmac.Generic.X86.scr .edi F.st0O ++ VG.Impl.Hmac.Generic.X86.scr .esi F.st1O))
  su3 : Ck [.ebp] (copy .ebp F.st0O .ebp F.stSO F.H.S)
  su4 : Ck [.ebp] (.block (VG.Impl.Hmac.Generic.X86.scr .edi F.stSO ++ [.mov .eax (.imm 0),
      .mov .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .ecx (Fns.argM 3), .mov .edx (Fns.argM 2)]))
  init : Ck [.ebp] (.block F.loopInit)
  b1 : Ck [.ebp, .ebx] (copy .ebp F.stSO .ebp F.stWO F.H.S)
  b2 : Ck [.ebp, .ebx] (.block F.updArgs)
  b4 : Ck [.ebp, .ebx] (.block F.finArgs)
  b6 : Ck [.ebp, .ebx] (copy .ebp F.uO .ebp F.tO F.H.D)
  b7 : Ck [.ebp, .ebx] (.block F.iterArgs)
  tail : Ck [.ebp, .ebx] (.seq F.outLen (.seq F.outLoop (.block F.advance)))
  restore : Ck [.ebp] (.block F.L.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : E s₀ = E s₀'
  args : ∀ i < 8, arg s₀ i = arg s₀' i

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.a {i : Nat} (hi : i < 8) : arg s₀' i = arg s₀ i := (hq.args i hi).symm

/-- `s₀'`'s public values are `s₀`'s. -/
macro "pub_simp" hq:term " at " h:ident : tactic => `(tactic|
  simp only [dO, A, scr, pw, salt, pwl, sl, ol, cc, out, kp, kl, nbk, dn, PubEq.a $hq (i := 0) (by decide),
    PubEq.a $hq (i := 1) (by decide), PubEq.a $hq (i := 2) (by decide), PubEq.a $hq (i := 3) (by decide),
    PubEq.a $hq (i := 4) (by decide), PubEq.a $hq (i := 5) (by decide), PubEq.a $hq (i := 6) (by decide),
    PubEq.a $hq (i := 7) (by decide)] at $h:ident)

theorem PubEq.E' : E s₀' = E s₀ := hq.esp.symm
theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a (by decide)
theorem PubEq.pwlEq : pwl s₀' = pwl s₀ := by show (arg s₀' 1).toNat = _; rw [hq.a (by decide)]
theorem PubEq.olEq : ol s₀' = ol s₀ := by show (arg s₀' 6).toNat = _; rw [hq.a (by decide)]
theorem PubEq.nbkEq : nbk F s₀' = nbk F s₀ := by show Whole.nb _ (ol s₀') = _; rw [hq.olEq]
theorem PubEq.dnEq (k : Nat) : dn F s₀' k = dn F s₀ k := by show Whole.done _ (ol s₀') k = _; rw [hq.olEq]

end

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre F t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 8 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 8⟩ : Region) = ⟨(E t).setWidth 64, 4 + 32⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_o h.o_a.symm
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree_argTaint (hag s s' h h')
      (by rw [(hk h).esp, (hk h').esp, hq.esp])
      (args_out hp (hk h).esp (hk h).wr) (args_out hp' (hk h').esp (hk h').wr)
      fun i hi => by rw [(hk h).argEq hp hi, (hk h').argEq hp' hi, hq.args i hi]) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_ebp {s s' : State} (h : KR F s₀ s) (h' : KR F s₀' s') : ∀ r ∈ [Reg.ebp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.ebp, h'.ebp, hq.scrEq]

end

/-! ## The key -/

/-- The password is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ pwl t₀

/-- The pieces of hashing the password: the state for its digest, then
`update` with the password, then `finalize`. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = arg t₀ 1 ∧
    s.gpr .edx = pw t₀ ∧ hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((pw t₀).setWidth 64) (pwl t₀)) ∧
    s.gpr .edi = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .eax = arg t₀ 1 ∧ s.gpr .ecx = 0 ∧ s.gpr .edx = dO t₀ F.hkO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem ((pw t₀).setWidth 64) (pwl t₀))) ∧ Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem ((pw t₀).setWidth 64) (pwl t₀))) ∧
    Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ s.gpr .ecx = arg t₀ 1 ∧ s.cf = some (decide (pwl t₀ < F.H.B + 1))

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀') (hc : Checks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (KR F s₀ s ∧ Long F s₀) ∧ (KR F s₀' s' ∧ Long F s₀')) F.hashKey
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  unfold Fns.hashKey
  have r1 := piece hp hp' hq (fun t₀ s => KR F t₀ s ∧ Long F t₀) (Hk1 F) (fun h => h.1)
    (fun s s' h h' => ag_ebp hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (hk1_ok h.1) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2 : RelCT isa (fun s s' => Hk1 F s₀ s ∧ Hk1 F s₀' s') (F.H.callInit .edi)
      fun s s' => Hk2 hF.hH s₀ s ∧ Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (sp := E s₀) (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, d⟩, _⟩, ⟨⟨k', d'⟩, _⟩⟩ =>
        ⟨hk2_args hp hz k d, by have := hk2_args hp' hz k' d'; pub_simp hq at this; exact this, k.esp,
          by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (hk2_ok hp hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d⟩, l⟩ => WP.mono (hk2_ok hp' hz hF.hH k d) fun t ⟨k', r, e⟩ => ⟨⟨k', r, e.trans d⟩, l⟩)
  have r3 := piece hp hp' hq (Hk2 hF.hH) (Hk3 hF.hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk3_ok hp₀ k d) fun t ⟨k', d', i, a, c, x, m⟩ =>
      ⟨⟨k', d', i, a, c, x, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => Hk3 hF.hH s₀ s ∧ Hk3 hF.hH s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => Hk4 hF.hH s₀ s ∧ Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, i, a, c, x, _⟩, _⟩, ⟨⟨k', d', i', a', c', x', _⟩, _⟩⟩ =>
        ⟨hk4_args hp hz hF.hH k d i a c x,
          by have := hk4_args hp' hz hF.hH k' d' i' a' c' x'; pub_simp hq at this; exact this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (hk4_ok hp hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
      (fun s ⟨⟨k, d, i, a, c, x, r⟩, l⟩ => WP.mono (hk4_ok hp' hz hF.hH k d i a c x r) fun t ⟨k', r', e⟩ =>
        ⟨⟨k', r', e.trans d⟩, l⟩)
  have r5 := piece hp hp' hq (Hk4 hF.hH) (Hk5 hF.hH) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.hk5
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk5_ok hp₀ k d) fun t ⟨k', d', a, c, x, m⟩ =>
      ⟨⟨k', d', a, c, x, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => Hk5 hF.hH s₀ s ∧ Hk5 hF.hH s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5))
      fun s s' => Hk6 hF.hH s₀ s ∧ Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, a, c, x, _⟩, _⟩, ⟨⟨k', d', a', c', x', _⟩, _⟩⟩ =>
        ⟨hk6_args hp hz hF.hH k d a c x,
          by have := hk6_args hp' hz hF.hH k' d' a' c' x'; pub_simp hq at this; exact this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (hk6_ok hp hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a, c, x, r⟩, l⟩ => WP.mono (hk6_ok hp' hz hF.hH k d a c x r) fun t h => ⟨h, l⟩)
  have r7 := piece hp hp' hq (Hk6 hF.hH) (Keyed hF) (fun h => h.1.1) (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (hk7_ok k) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ pwl t₀ < F.H.B + 1 := by omega
      have ekp : kp F t₀ = dO t₀ F.hkO := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = F.H.D := by simp only [kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ (by omega), m, b, blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega)
        (hash_len hF.hH b)])
  exact r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))

theorem key_rel :
    RelCT isa (fun s s' => KR F s₀ s ∧ KR F s₀' s') F.key fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.key
  have rc := piece hp hp' hq (fun t₀ s => KR F t₀ s) (Cmp F) id (fun s s' h h' => ag_ebp hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (cmp_ok hp₀ hz k) fun t ⟨k', c, f, _⟩ => ⟨k', c, f⟩)
  have ev : ∀ {t₀ t : State}, Cmp F t₀ t → isa.eval .ae t = some (decide (F.H.B + 1 ≤ pwl t₀)) := by
    intro t₀ t h
    show t.cf.map (!·) = _
    rw [h.2.2]; simp only [Option.map_some, ← decide_not, Nat.not_lt]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.pwlEq]) ?_ ?_)
  · refine (hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, this⟩, h.1.2.1, by show F.H.B + 1 ≤ pwl s₀'; rw [hq.pwlEq]; exact this⟩
  · refine (piece hp hp' hq (fun t₀ s => Cmp F t₀ s ∧ pwl t₀ < F.H.B + 1) (Keyed hF) (fun h => h.1.1)
      (fun s s' h h' => ag_ebp hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, c, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : kp F t₀ = pw t₀ := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = pwl t₀ := by simp only [kl, hlt, ↓reduceIte]
      refine wp_arg hp₀ k (by decide) fun s₂ u₂ => WP.block_nil ⟨k.upd (by decide) u₂, by rw [u₂.gpr, ekp], ?_, ?_⟩
      · rw [u₂.other _ (by decide), c, ekl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [u₂.mem, ekp, ekl, k.pwBytes hp₀]
    · have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      have hlt : pwl s₀ < F.H.B + 1 := by omega
      exact ⟨⟨h.1.1, hlt⟩, h.1.2, by rw [hq.pwlEq]; exact hlt⟩

end

/-! ## HMAC's states for the key, and the salt -/

abbrev Su1 (hF : FnsOK F) (t₀ s : State) : Prop :=
  Keyed hF t₀ s ∧ s.gpr .edi = dO t₀ F.st0O ∧ s.gpr .esi = dO t₀ F.st1O
abbrev Su2 (hF : FnsOK F) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (K0 hF t₀) opad) ∧ (K0 hF t₀).length = F.H.B
abbrev Su3 (hF : FnsOK F) (t₀ s : State) : Prop :=
  KR F t₀ s ∧ hF.hH.SH.Repr s.mem (A t₀ F.st0O) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.st1O) (xorPad (K0 hF t₀) opad) ∧
    hF.hH.SH.Repr s.mem (A t₀ F.stSO) (xorPad (K0 hF t₀) ipad) ∧ (K0 hF t₀).length = F.H.B
abbrev Su4 (hF : FnsOK F) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ s.gpr .edi = dO t₀ F.stSO ∧ s.gpr .esi = BitVec.ofNat 32 F.H.B ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = arg t₀ 3 ∧ s.gpr .edx = salt t₀) ∧
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
  have r1 := piece hp hp' hq (Keyed hF) (Su1 hF) (fun h => h.kr) (fun s s' h h' => ag_ebp hq h.kr h'.kr) hc.su1
    (fun _ s h => su1_ok hF h)
  have r2 : RelCT isa (fun s s' => Su1 hF s₀ s ∧ Su1 hF s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call F.hiN F.hiC) (.pop .eax 5))
      fun s s' => Su2 hF s₀ s ∧ Su2 hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := E s₀) fun s s' ⟨⟨h, d, i⟩, ⟨h', d', i'⟩⟩ =>
        ⟨su2_args hp hz hF h d i,
          by have := su2_args hp' hz hF h' d' i'; pub_simp hq at this; exact this,
          h.kr.esp, by rw [h'.kr.esp, hq.E']⟩)
      (fun s ⟨h, d, i⟩ => WP.mono (su2_ok hp hz hF h d i) fun t ⟨k, r0, r1⟩ => ⟨k, r0, r1, K0_length hp hz hF h⟩)
      (fun s ⟨h, d, i⟩ => WP.mono (su2_ok hp' hz hF h d i) fun t ⟨k, r0, r1⟩ => ⟨k, r0, r1, K0_length hp' hz hF h⟩)
  have r3 := piece hp hp' hq (Su2 hF) (Su3 hF) (fun h => h.1) (fun s s' h h' => ag_ebp hq h.1 h'.1) hc.su3
    (fun hp₀ s ⟨k, r0, r1, l⟩ => WP.mono (su3_ok hp₀ hz hF k r0 r1) fun t ⟨k', r0', r1', rS⟩ =>
      ⟨k', r0', r1', rS, l⟩)
  have r4 := piece hp hp' hq (Su3 hF) (Su4 hF) (fun h => h.1) (fun s s' h h' => ag_ebp hq h.1 h'.1) hc.su4
    (fun hp₀ s ⟨k, r0, r1, rS, l⟩ => WP.mono (su4_ok hp₀ k) fun t ⟨k', d, i, a, c, x, m⟩ =>
      ⟨⟨k', d, i, a, c, x⟩, m ▸ r0, m ▸ r1, m ▸ rS, l⟩)
  have r5 : RelCT isa (fun s s' => Su4 hF s₀ s ∧ Su4 hF s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => Su5 hF s₀ s ∧ Su5 hF s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨k, d, i, a, c, x⟩, _⟩, ⟨⟨k', d', i', a', c', x'⟩, _⟩⟩ =>
        ⟨su5_args hp hz hF k d i a c x,
          by have := su5_args hp' hz hF k' d' i' a' c' x'; pub_simp hq at this; exact this,
          k.esp, by rw [k'.esp, hq.E']⟩)
      (fun s ⟨⟨k, d, i, a, c, x⟩, r0, r1, rS, l⟩ => WP.mono (su5_ok hp hz hF k d i a c x l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
      (fun s ⟨⟨k, d, i, a, c, x⟩, r0, r1, rS, l⟩ => WP.mono (su5_ok hp' hz hF k d i a c x l r0 r1 rS)
        fun t ⟨k', st⟩ => ⟨k', st, l⟩)
  exact r1.seq (r2.seq (r3.seq (r4.seq r5)))

theorem loopInit_rel :
    RelCT isa (fun s s' => Su5 hF s₀ s ∧ Su5 hF s₀' s') (.block F.loopInit) fun s s' =>
      (Inv hF s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0))) ∧ (Inv hF s₀' 0 s' ∧ s'.zf = some (decide (ol s₀' = 0))) :=
  piece hp hp' hq (Su5 hF) (fun t₀ s => Inv hF t₀ 0 s ∧ s.zf = some (decide (ol t₀ = 0))) (fun h => h.1)
    (fun _ _ h h' => ag_ebp hq h.1 h'.1) hc.init
    (fun hp₀ _ ⟨k, st, l⟩ => loopInit_ok hp₀ hF.sizes k st l)

end

/-! ## A block of the output -/

/-- The pieces of a block. -/
abbrev Bk (hF : FnsOK F) (k : Nat) (P : State → State → Prop) (t₀ s : State) : Prop :=
  (Inv hF t₀ k s ∧ P t₀ s) ∧ k < nbk F t₀
abbrev Bk1 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀)
abbrev Bk2 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  (s.gpr .edi = dO t₀ F.stWO ∧ s.gpr .esi = arg t₀ 3 + BitVec.ofNat 32 F.H.B ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = BitVec.ofNat 32 4 ∧ s.gpr .edx = dO t₀ F.intO) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀)
abbrev Bk3 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk4 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  (s.gpr .edx = dO t₀ F.stWO ∧ s.gpr .esi = dO t₀ F.st1O ∧ s.gpr .eax = arg t₀ 3 + BitVec.ofNat 32 (F.H.B + 4) ∧
    s.gpr .ecx = 0 ∧ s.gpr .edi = dO t₀ F.uO) ∧
  hF.hH.SH.Repr s.mem (A t₀ F.stWO) (xorPad (K0 hF t₀) ipad ++ saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk5 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  bytesAt s.mem (A t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk6 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  bytesAt s.mem (A t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (A t₀ F.tO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk7 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s =>
  (s.gpr .esi = dO t₀ F.st0O ∧ s.gpr .eax = dO t₀ F.uO ∧ s.gpr .ecx = arg t₀ 4 - 1 ∧ s.gpr .edx = dO t₀ F.tO) ∧
  bytesAt s.mem (A t₀ F.uO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1)) ∧
    bytesAt s.mem (A t₀ F.tO) F.H.D = prf hF t₀ (saltB t₀ ++ Spec.Pbkdf2.int (k + 1))
abbrev Bk8 (hF : FnsOK F) (k : Nat) := Bk hF k fun t₀ s => bytesAt s.mem (A t₀ F.tO) F.H.D = Tk hF t₀ (k + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀') (hc : Checks F)
include hp hp' hq hc

omit hp hp' hc in
theorem ag_loop {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (h' : Inv hF s₀' k s') :
    ∀ r ∈ [Reg.ebp, .ebx], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.kr.ebp, h'.kr.ebp, hq.scrEq]
  · rw [h.ebx, h'.ebx, hq.dnEq]

theorem block_rel (k : Nat) :
    RelCT isa (fun s s' => (Inv hF s₀ k s ∧ k < nbk F s₀) ∧ (Inv hF s₀' k s' ∧ k < nbk F s₀')) F.block
      fun s s' => (Inv hF s₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = nbk F s₀))) ∧
        (Inv hF s₀' (k + 1) s' ∧ s'.zf = some (decide (k + 1 = nbk F s₀'))) := by
  have hz := hF.sizes
  unfold Fns.block
  have r1 := piece hp hp' hq (fun t₀ s => Inv hF t₀ k s ∧ k < nbk F t₀) (Bk1 hF k) (fun h => h.1.kr)
    (fun _ _ h h' => ag_loop hq h.1 h'.1) hc.b1
    (fun hp₀ _ ⟨i, l⟩ => WP.mono (b1_ok hp₀ hz i) fun _ ⟨i', r⟩ => ⟨⟨i', r⟩, l⟩)
  have r2 := piece hp hp' hq (Bk1 hF k) (Bk2 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b2
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (b2_ok hp₀ hz i) fun _ ⟨i', d, si, a, c, x, m⟩ =>
      ⟨⟨i', ⟨d, si, a, c, x⟩, by rw [m]; exact r⟩, l⟩)
  have r3 : RelCT isa (fun s s' => Bk2 hF k s₀ s ∧ Bk2 hF k s₀' s')
      (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
      fun s s' => Bk3 hF k s₀ s ∧ Bk3 hF k s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := E s₀) fun s s' ⟨⟨⟨i, ⟨d, si, a, c, x⟩, _⟩, _⟩, ⟨⟨i', ⟨d', si', a', c', x'⟩, _⟩, _⟩⟩ =>
        ⟨b3_args hp hz i d si a c x,
          by have := b3_args hp' hz i' d' si' a' c' x'; pub_simp hq at this; exact this,
          i.kr.esp, by rw [i'.kr.esp, hq.E']⟩)
      (fun _ ⟨⟨i, ⟨d, si, a, c, x⟩, r⟩, l⟩ => WP.mono (b3_ok hp hz i d si a c x r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨d, si, a, c, x⟩, r⟩, l⟩ => WP.mono (b3_ok hp' hz i d si a c x r) fun _ h => ⟨h, l⟩)
  have r4 := piece hp hp' hq (Bk3 hF k) (Bk4 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b4
    (fun hp₀ _ ⟨⟨i, r⟩, l⟩ => WP.mono (b4_ok hp₀ hz i) fun _ ⟨i', x, si, a, c, d, m⟩ =>
      ⟨⟨i', ⟨x, si, a, c, d⟩, by rw [m]; exact r⟩, l⟩)
  have r5 : RelCT isa (fun s s' => Bk4 hF k s₀ s ∧ Bk4 hF k s₀' s')
      (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call F.hfN F.hfC) (.pop .eax 6))
      fun s s' => Bk5 hF k s₀ s ∧ Bk5 hF k s₀' s' :=
    rel_wp (hf_rel hF.hf (sp := E s₀) fun s s' ⟨⟨⟨i, ⟨x, si, a, c, d⟩, _⟩, _⟩, ⟨⟨i', ⟨x', si', a', c', d'⟩, _⟩, _⟩⟩ =>
        ⟨b5_args hp hz i x si a c d,
          by have := b5_args hp' hz i' x' si' a' c' d'; pub_simp hq at this; exact this,
          i.kr.esp, by rw [i'.kr.esp, hq.E']⟩)
      (fun _ ⟨⟨i, ⟨x, si, a, c, d⟩, r⟩, l⟩ => WP.mono (b5_ok hp hz i x si a c d r) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨x, si, a, c, d⟩, r⟩, l⟩ => WP.mono (b5_ok hp' hz i x si a c d r) fun _ h => ⟨h, l⟩)
  have r6 := piece hp hp' hq (Bk5 hF k) (Bk6 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b6
    (fun hp₀ _ ⟨⟨i, u⟩, l⟩ => WP.mono (b6_ok hp₀ hz i u) fun _ ⟨i', u', t'⟩ => ⟨⟨i', u', t'⟩, l⟩)
  have r7 := piece hp hp' hq (Bk6 hF k) (Bk7 hF k) (fun h => h.1.1.kr) (fun _ _ h h' => ag_loop hq h.1.1 h'.1.1) hc.b7
    (fun hp₀ _ ⟨⟨i, u, t⟩, l⟩ => WP.mono (b7_ok hp₀ hz i) fun _ ⟨i', si, a, c, x, m⟩ =>
      ⟨⟨i', ⟨si, a, c, x⟩, by rw [m]; exact u, by rw [m]; exact t⟩, l⟩)
  have r8 : RelCT isa (fun s s' => Bk7 hF k s₀ s ∧ Bk7 hF k s₀' s')
      (.frame (.push [.ebp, .edx, .ecx, .eax, .esi]) (.call F.itN F.itC) (.pop .eax 5))
      fun s s' => Bk8 hF k s₀ s ∧ Bk8 hF k s₀' s' :=
    rel_wp (it_rel hF.it (sp := E s₀) fun s s' ⟨⟨⟨i, ⟨si, a, c, x⟩, _⟩, _⟩, ⟨⟨i', ⟨si', a', c', x'⟩, _⟩, _⟩⟩ =>
        ⟨b8_args hp hz i si a c x,
          by have := b8_args hp' hz i' si' a' c' x'; pub_simp hq at this; exact this,
          i.kr.esp, by rw [i'.kr.esp, hq.E']⟩)
      (fun _ ⟨⟨i, ⟨si, a, c, x⟩, u, t⟩, l⟩ => WP.mono (b8_ok hp hz i si a c x u t) fun _ h => ⟨h, l⟩)
      (fun _ ⟨⟨i, ⟨si, a, c, x⟩, u, t⟩, l⟩ => WP.mono (b8_ok hp' hz i si a c x u t) fun _ h => ⟨h, l⟩)
  have r9 := piece hp hp' hq (Bk8 hF k) (fun t₀ s => Inv hF t₀ (k + 1) s ∧ s.zf = some (decide (k + 1 = nbk F t₀)))
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
    show eval .ne _ = _; rw [eval_ne, z]; rfl
  have e' : isa.eval .ne s₂' = some (!decide (k + 1 = nbk F s₀)) := by
    show eval .ne _ = _; rw [eval_ne, z', hq.nbkEq]; rfl
  rw [e, e']
  refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
  · have hl : k + 1 = nbk F s₀ := by simpa using hf
    exact ⟨hl ▸ j, by rw [hq.nbkEq, ← hl]; exact j'⟩
  · have hl : k + 1 ≠ nbk F s₀ := by simpa using ht
    exact ⟨nbk F s₀ - (k + 1), by omega, k + 1, rfl, by omega, j, j'⟩

omit hp hp' hq hc in
theorem skip_check : ∃ hc, (VG.Taint.check taint (τr []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem loop_rel :
    RelCT isa (fun s s' => (Inv hF s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0))) ∧
        (Inv hF s₀' 0 s' ∧ s'.zf = some (decide (ol s₀' = 0))))
      (.ite .e (.block []) (.loop F.block .ne))
      fun s s' => Inv hF s₀ (nbk F s₀) s ∧ Inv hF s₀' (nbk F s₀') s' := by
  have hD := hF.sizes.D
  have e0 : nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  have ev : ∀ {t : State} {o : Nat}, t.zf = some (decide (o = 0)) → isa.eval .e t = some (decide (o = 0)) :=
    fun h => by show eval .e _ = _; rw [eval_e, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hq.olEq]) ?_ ?_
  · by_cases e : ol s₀ = 0
    · have n0 : nbk F s₀ = 0 := e0.2 e
      have n0' : nbk F s₀' = 0 := by rw [hq.nbkEq]; exact n0
      exact (rel_agree (c := .block [])
        (F := fun s => Inv hF s₀ 0 s ∧ s.zf = some (decide (ol s₀ = 0)))
        (F' := fun s => Inv hF s₀' 0 s ∧ s.zf = some (decide (ol s₀' = 0)))
        (G := Inv hF s₀ (nbk F s₀)) (G' := Inv hF s₀' (nbk F s₀')) (τr [])
        (fun _ _ _ _ => agree_regs (by simp)) skip_check
        (fun _ h => WP.block_nil (n0 ▸ h.1)) (fun _ h => WP.block_nil (n0' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
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
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := KR F s₀) (G' := KR F s₀')
    (argTaint [] (4 + 4 * 8)) (fun s s' e e' => by
        rw [e, e']
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hF s₀ (nbk F s₀) s ∧ Inv hF s₀' (nbk F s₀') s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint [.ebp] (4 + 4 * 8)) (fun s s' h => agree_argTaint (ag_ebp hq h.1.kr h.2.kr)
      (by rw [h.1.kr.esp, h.2.kr.esp, hq.esp]) (args_out hp h.1.kr.esp h.1.kr.wr) (args_out hp' h.2.kr.esp h.2.kr.wr)
      fun i hi => by rw [h.1.kr.argEq hp hi, h.2.kr.argEq hp' hi, hq.args i hi]) hr
  unfold Fns.pbkdf2
  exact pro.seq ((key_rel hp hp' hq hc).seq ((setup_rel hp hp' hq hc).seq ((loopInit_rel hp hp' hq hc).seq
    ((loop_rel hp hp' hq hc).seq restore))))

end

/-- `pbkdf2` is verified against `pbkN`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verifiedN (hF : FnsOK F) (hc : Checks F) (hsat : ∃ s, (pbkN hF.hH.SH (F.W + F.H.S)).pre s) :
    Verified X86.target F.pbkdf2 (pbkN hF.hH.SH (F.W + F.H.S)) := by
  refine ⟨fun s hs => correct (pre_of hF hs) hF.sizes, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2⟩ := hpub
  exact (ct (hF := hF) (pre_of hF h₁) (pre_of hF h₂) ⟨h1, h2⟩ hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `pbkdf2` is verified against the shared contract, given the taint checks
and a state satisfying the shared contract. -/
theorem verified (hF : FnsOK F) (hc : Checks F) {S : Spec.Hmac.StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2Contract S W X86.abi 76).pre s) :
    Verified X86.target F.pbkdf2 (Spec.Pbkdf2.pbkdf2Contract S W X86.abi 76) := by
  subst hS hW
  have imp := pbkImp hF.hH.SH (F.W + F.H.S) hsat
  have gsat : ∃ s, (pbkG hF.hH.SH (F.W + F.H.S)).pre s := hsat.elim fun s h => ⟨s, imp.pre s h⟩
  exact (verified_pbkG _ _ (verifiedN hF hc (gsat.elim fun s h => ⟨_, pbkN_pre _ _ h⟩)) gsat).of_implies imp

/-- Memory holding the arguments `0x1000, 0, 0x1100, 0, 1, 0x1200, 0, 0x2000`
of `pbkdf2` at `0x8004`. -/
def pbkMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x800D then 0x11 else if a = 0x8014 then 0x01 else
  if a = 0x8019 then 0x12 else if a = 0x8021 then 0x20 else 0

/-- A state satisfying `pbkdf2`'s precondition with `8 W` bytes of scratch
space: an empty password, salt and output, and one iteration. -/
def pbkSat (W : Nat) : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pbkMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩]
  wr := [⟨0x1200, 0⟩, ⟨0x2000, W * 8⟩, ⟨0x8004, 32⟩]

end VG.Proof.Pbkdf2.Whole.X86
