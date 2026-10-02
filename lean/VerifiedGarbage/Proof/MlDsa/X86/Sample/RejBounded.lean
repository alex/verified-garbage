import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.HalfByteVal
import VerifiedGarbage.Impl.MlDsa.X86.Sample.RejBounded

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_rej_bounded_poly`

The body is the SHAKE256 output of the seed at `scratch + 840`
(`sponge_piece`), then a branch on the public `η` to its loop, iteration `t`
of which starts with the coefficients `LA s₀ t = rbFold η [] ((H(ρ, 544)).take
t)` (`Proof/MlDsa/Sample/RejBounded.lean`) stored at `a`, `edi` after them and
`ecx` counting them (`Loop`); the end returns whether there are 256. A
half-byte is tried (`try_piece`) as `hbTry` does: its coefficient, computed
without a branch (`hbVal`), is stored if it is accepted.

Constant time: two runs whose leaks (`rejBoundedLeak`) agree accept the
half-bytes of each byte alike (`oks_at`) and so have sampled as many
coefficients after each iteration (`LA_len`): the branches, the counter
and the addresses of the stores agree; the coefficient is computed and
stored by code the taint analysis proves constant time from `edi` alone.
-/

namespace VG.Proof.MlDsa.X86.Sample.RejBounded

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp rbVal rbTry rbLoad rbHi rbBody rbLoop rbBound retJ qImm sponge csub etaSub)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt halfByteOk rejBoundedLeak)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)
open VG.Proof.MlDsa.X86.Sample.RejNtt (nil_piece zw_ofNat)

/-- The layout: `rejBounded(seed, eta, a, scratch)`, 66 bytes of seed, 544
bytes of SHAKE256. -/
def L : Lay := { nA := 4, iA := 2, iS := 3, rate := 136, outlen := 544, mlen := some 66 }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by cases hk; decide,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- `η`. -/
abbrev η (s₀ : State) : Nat := (arg s₀ 1).toNat

/-- The precondition. -/
def BPre (s₀ : State) : Prop := Pre L s₀ ∧ (η s₀ = 2 ∨ η s₀ = 4)

/-- The pointers and `esp` agree, and so does the leak. -/
def BPub (s₀ s₀' : State) : Prop :=
  PubP L s₀ s₀' ∧ rejBoundedLeak (η s₀) (L.Msg s₀) = rejBoundedLeak (η s₀') (L.Msg s₀')

/-! ## The XOF output and the coefficients it gives -/

/-- The XOF output. -/
abbrev X (s₀ : State) : List Byte := L.out s₀

/-- Byte `t` of it. -/
abbrev zb (s₀ : State) (t : Nat) : Byte := (X s₀).getD t 0

/-- The coefficients sampled after `t` iterations. -/
abbrev LA (s₀ : State) (t : Nat) : List Zq := rbFold (η s₀) [] ((X s₀).take t)

theorem X_eq (s₀ : State) : X s₀ = H (L.Msg s₀) 544 := (H_eq _ _).symm

theorem X_length (s₀ : State) : (X s₀).length = 544 := by rw [X_eq]; exact H_length _ _

theorem LA_zero (s₀ : State) : LA s₀ 0 = [] := by simp [LA, rbFold]

theorem LA_succ (s₀ : State) {t : Nat} (ht : t < 544) : LA s₀ (t + 1) = rbStep (η s₀) (LA s₀ t) (zb s₀ t) := by
  simp only [LA]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [X_length]; exact ht), Option.toList_some,
    rbFold_snoc]
  show _ = rbStep _ _ ((X s₀).getD t 0)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [X_length]; exact ht), Option.getD_some]

theorem LA_length_le (s₀ : State) (t : Nat) : (LA s₀ t).length ≤ 256 := rbFold_length_le (by simp) _

namespace BPub
variable {s₀ s₀' : State} (hq : BPub s₀ s₀')
include hq

theorem eη : η s₀ = η s₀' := by rw [η, η, hq.1.2 1 (by decide)]

theorem oks : (X s₀).map (hbOks (η s₀)) = (X s₀').map (hbOks (η s₀)) := by
  have h := hq.2
  rw [← hq.eη] at h
  rw [X_eq, X_eq]
  exact leak_hbOks h (B := 544) (by decide)

theorem oks_at {t : Nat} (ht : t < 544) : hbOks (η s₀) (zb s₀ t) = hbOks (η s₀) (zb s₀' t) := by
  have := congrArg (fun l => l[t]?) hq.oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < (X s₀).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X s₀').length by rw [X_length]; exact ht), Option.map_some,
    Option.some.injEq] at this
  simp only [zb, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < (X s₀).length by rw [X_length]; exact ht),
    List.getElem?_eq_getElem (show t < (X s₀').length by rw [X_length]; exact ht), Option.getD_some]
  exact this

theorem LA_len (t : Nat) : (LA s₀ t).length = (LA s₀' t).length := by
  simp only [LA]
  rw [← hq.eη]
  exact rbFold_length_congr rfl (by rw [List.map_take, List.map_take, hq.oks])

end BPub

/-! ## The state of the loop -/

/-- After `t` iterations, with the coefficients `La` stored. -/
structure Loop (s₀ : State) (t : Nat) (La : List Zq) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 544, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = zb s₀ p
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (840 + t)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (544 - t)
  len : La.length ≤ 256
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (4 * La.length)
  ecx : s.gpr .ecx = BitVec.ofNat 32 La.length
  stored : Stored s.mem (L.aA s₀) La

theorem Loop.flags {s₀ s s' : State} {t : Nat} {La : List Zq} (h : Loop s₀ t La s)
    (hsp : s'.gpr .esp = s.gpr .esp) (hsi : s'.gpr .esi = s.gpr .esi) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hdi : s'.gpr .edi = s.gpr .edi) (hcx : s'.gpr .ecx = s.gpr .ecx)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : Loop s₀ t La s' :=
  ⟨⟨by rw [hsp, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm]; exact h.frame⟩,
    by rw [hm]; exact h.out, by rw [hsi, h.esi], by rw [hbp, h.ebp], h.len, by rw [hdi, h.edi], by rw [hcx, h.ecx],
    by rw [hm]; exact h.stored⟩

/-! ## A half-byte -/

/-- The coefficient of the half-byte in `edx`, into `ebx`. -/
theorem rbVal_run {e : Nat} (he : e = 2 ∨ e = 4) (s : State) :
    WP isa (.block (rbVal e)) s fun s' => s'.gpr .ebx = hbVal e (s.gpr .edx) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r := by
  have hqi : qImm = 8380417#32 := rfl
  apply WP.of_runBlock
  rcases he with rfl | rfl
  · simp (config := {decide := true}) only [rbVal, Impl.MlDsa.X86.Sample.csub, etaSub, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.setReg,
      arithFlags, State.setFlags, Option.bind_some, Option.map_some, BitVec.sub_self, hqi, ite_true, ite_false,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp [hbVal, etaV, csubV], trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩
  · simp (config := {decide := true}) only [rbVal, etaSub, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.setReg,
      arithFlags, State.setFlags, Option.bind_some, Option.map_some, BitVec.sub_self, hqi, ite_true, ite_false,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp [hbVal, etaV], trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2]⟩

/-- The store block: `a[j] ← ebx`, `j` incremented. -/
abbrev stBlk : List Instr := [.store (at_ .edi 0) .ebx, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]

theorem store_ok {s₀ : State} (hp : BPre s₀) {t : Nat} {La : List Zq} (x : Zq) (hl : La.length < 256) {s : State}
    (h : Loop s₀ t La s) (hbx : s.gpr .ebx = zw x) :
    WP isa (.block stBlk) s fun s' => Loop s₀ t (La ++ [x]) s' ∧ s'.gpr .eax = s.gpr .eax := by
  have ha := hp.1.a_fit
  have ea : (L.aP s₀ + BitVec.ofNat 32 (4 * La.length) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (L.aA s₀) La.length := by
    rw [ea_add (by simp only [L] at ha ⊢; omega)]; rfl
  have hin : InRegions s.wr (coeffAddr (L.aA s₀) La.length) 4 := hp.1.inA h.wr hl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, ea, hin,
    hbx, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := L.aR s₀) (by simp) _
    (coeff_contains _ hl)⟩, fun p hp' => ?_, by simp [h.esi], by simp [h.ebp],
    (by simp only [List.length_append, List.length_singleton]; omega), ?_, ?_, stored_snoc h.stored hl x⟩, by simp⟩
  · refine (((Frame.refl _ _).writeW (List.mem_singleton_self (L.aR s₀)) _ (coeff_contains _ hl)) _
      fun r hr hc => ?_).trans (h.out p hp')
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.1.a_s _ hc ((hp.1.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
  · simp only [ite_true, List.length_append, List.length_singleton]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx, List.length_append, List.length_singleton]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]

/-- An accepted half-byte `b` in `edx`: its coefficient stored. -/
theorem acc_ok {e : Nat} (he : e = 2 ∨ e = 4) {s₀ : State} (hp : BPre s₀) {t : Nat} {La : List Zq} {b : Nat}
    (hb : b < rbB e) (hl : La.length < 256) {s : State} (h : Loop s₀ t La s)
    (hdx : s.gpr .edx = BitVec.ofNat 32 b) :
    WP isa (.block (rbVal e ++ stBlk)) s fun s' =>
      Loop s₀ t (La ++ [ofInt (rbC e b)]) s' ∧ s'.gpr .eax = s.gpr .eax := by
  rw [WP.block_append_iff]
  refine (rbVal_run he s).mono fun s1 ⟨hbx, hm, hr, hw, hg⟩ => ?_
  refine (store_ok hp _ hl (h.flags (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
    (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) hm hr hw)
    (by rw [hbx, hdx, hbVal_eq he hb])).mono fun s2 ⟨h2, e2⟩ => ⟨h2, by rw [e2, hg _ (by decide) (by decide)]⟩

/-- A half-byte `hb s₀` in `edx` tried, with `eax = E s₀` and the facts `X s₀` kept. -/
theorem try_piece {e : Nat} (he : e = 2 ∨ e = 4) (t : Nat) (La : State → List Zq) (hb E : State → Nat)
    (X : State → Prop)
    (hpub : ∀ s₀ s₀', BPre s₀ → BPre s₀' → BPub s₀ s₀' →
      (La s₀).length = (La s₀').length ∧ decide (hb s₀ < rbB (η s₀)) = decide (hb s₀' < rbB (η s₀')))
    (tc : TaintOk [] (.block [.alu .cmp .edx (.imm (rbBound e))]))
    (ts : TaintOk [.edi] (.block (rbVal e ++ stBlk))) :
    Piece BPre BPub
      (fun s₀ s => ((Loop s₀ t (La s₀) s ∧ s.gpr .edx = BitVec.ofNat 32 (hb s₀) ∧
        s.gpr .eax = BitVec.ofNat 32 (E s₀) ∧ (La s₀).length < 256 ∧ hb s₀ < 16) ∧ η s₀ = e) ∧ X s₀)
      (fun s₀ s => ((Loop s₀ t (hbTry (η s₀) (La s₀) (hb s₀)) s ∧ s.gpr .eax = BitVec.ofNat 32 (E s₀)) ∧
        η s₀ = e) ∧ X s₀)
      (rbTry e) := by
  obtain ⟨_, tc⟩ := tc
  obtain ⟨_, ts⟩ := ts
  have hbnd : (rbBound e).toNat = rbB e := by rcases he with rfl | rfl <;> rfl
  refine Piece.seq (B := fun s₀ s => (((Loop s₀ t (La s₀) s ∧ s.gpr .edx = BitVec.ofNat 32 (hb s₀) ∧
      s.gpr .eax = BitVec.ofNat 32 (E s₀) ∧ (La s₀).length < 256 ∧ hb s₀ < 16) ∧ η s₀ = e) ∧ X s₀) ∧
      eval .b s = some (decide (hb s₀ < rbB (η s₀)))) ?_
    (Piece.ite (fun s₀ => decide (hb s₀ < rbB (η s₀))) (fun _ _ _ h => h.2)
      (fun s₀ s₀' h₀ h₀' hq => (hpub s₀ s₀' h₀ h₀' hq).2) ?_ ?_)
  · refine Piece.taint [] (fun s₀ s hp ha => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) tc
    obtain ⟨⟨⟨h, hdx, hax, hl, h16⟩, hη⟩, hx⟩ := ha
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨⟨h.flags rfl rfl rfl rfl rfl rfl rfl rfl, hdx, hax, hl, h16⟩, hη⟩, hx⟩, ?_⟩
    simp only [eval, hdx, hbnd, toNat_ofNat32 (show hb s₀ < 2 ^ 32 by omega), hη]
  · refine Piece.taint [.edi] (fun s₀ s hp ⟨⟨⟨⟨⟨h, hdx, hax, hl, _⟩, hη⟩, hx⟩, _⟩, hb'⟩ => ?_)
      (fun s₀ s₀' s s' h₀ h₀' hq ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨h', _⟩, _⟩, _⟩, _⟩, _⟩ r hr => ?_) ts
    · have hb2 : hb s₀ < rbB e := hη ▸ of_decide_eq_true hb'
      refine (acc_ok he hp hb2 hl h hdx).mono fun s' ⟨h1, h2⟩ => ⟨⟨⟨?_, by rw [h2, hax]⟩, hη⟩, hx⟩
      rw [hη, hbTry_eq he, ifT hb2]; exact h1
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.1.aP hL, (hpub s₀ s₀' h₀ h₀' hq).1]
  · exact nil_piece fun s₀ s _ ⟨⟨⟨⟨⟨h, _, hax, _⟩, hη⟩, hx⟩, _⟩, hb'⟩ => by
      refine ⟨⟨⟨?_, hax⟩, hη⟩, hx⟩
      rw [hη, hbTry_eq he, ifF (hη ▸ of_decide_eq_false hb')]; exact h

/-! ## An iteration -/

/-- The half-bytes of byte `t`. -/
abbrev lo (s₀ : State) (t : Nat) : Nat := (zb s₀ t).toNat % 16
abbrev hi (s₀ : State) (t : Nat) : Nat := (zb s₀ t).toNat / 16

/-- The coefficients after the low half-byte of byte `t`. -/
abbrev L1 (s₀ : State) (t : Nat) : List Zq := hbTry (η s₀) (LA s₀ t) (lo s₀ t)

theorem ok_bound {s₀ : State} (hp : BPre s₀) (b : Nat) :
    halfByteOk (η s₀) b = if b < rbB (η s₀) then 1 else 0 := halfByteOk_eq hp.2 b

theorem lo_pub {s₀ s₀' : State} (hp : BPre s₀) (hq : BPub s₀ s₀') {t : Nat} (ht : t < 544) :
    decide (lo s₀ t < rbB (η s₀)) = decide (lo s₀' t < rbB (η s₀')) := by
  have h := congrArg Prod.fst (hq.oks_at ht)
  simp only [hbOks] at h
  rw [ok_bound hp, ok_bound hp] at h
  rw [← hq.eη]
  by_cases h1 : lo s₀ t < rbB (η s₀) <;> by_cases h2 : lo s₀' t < rbB (η s₀) <;>
    simp only [h1, h2, ↓reduceIte, decide_true, decide_false] at h ⊢ <;> omega

theorem hi_pub {s₀ s₀' : State} (hp : BPre s₀) (hq : BPub s₀ s₀') {t : Nat} (ht : t < 544) :
    decide (hi s₀ t < rbB (η s₀)) = decide (hi s₀' t < rbB (η s₀')) := by
  have h := congrArg Prod.snd (hq.oks_at ht)
  simp only [hbOks] at h
  rw [ok_bound hp, ok_bound hp] at h
  rw [← hq.eη]
  by_cases h1 : hi s₀ t < rbB (η s₀) <;> by_cases h2 : hi s₀' t < rbB (η s₀) <;>
    simp only [h1, h2, ↓reduceIte, decide_true, decide_false] at h ⊢ <;> omega

theorem L1_len {s₀ s₀' : State} (hq : BPub s₀ s₀') {t : Nat} (ht : t < 544) :
    (L1 s₀ t).length = (L1 s₀' t).length := by
  have h := congrArg Prod.fst (hq.oks_at ht)
  simp only [hbOks] at h
  simp only [L1]
  rw [hbTry_length, hbTry_length, hq.LA_len t, h, hq.eη]

theorem LA_step {s₀ : State} {t : Nat} (ht : t < 544) :
    LA s₀ (t + 1) = if (LA s₀ t).length < 256 then
      (if (L1 s₀ t).length < 256 then hbTry (η s₀) (L1 s₀ t) (hi s₀ t) else L1 s₀ t) else LA s₀ t := by
  rw [LA_succ s₀ ht, rbStep]

theorem load_ok {s₀ : State} (hp : BPre s₀) {t : Nat} (ht : t < 544) {s : State} (h : Loop s₀ t (LA s₀ t) s) :
    WP isa (.block rbLoad) s fun s' => Loop s₀ t (LA s₀ t) s' ∧ s'.gpr .edx = BitVec.ofNat 32 (lo s₀ t) ∧
      s'.gpr .eax = BitVec.ofNat 32 (zb s₀ t).toNat ∧ eval .b s' = some (decide ((LA s₀ t).length < 256)) := by
  have hs := hp.1.s_fit
  have e0 : (L.sP s₀ + BitVec.ofNat 32 (840 + t) + BitVec.ofNat 32 0).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (840 + t) := by
    rw [ea_add (by simp only [L] at hs ⊢; omega)]; rfl
  have i0 := hp.1.inS' h.wr (o := 840 + t) (n := 1) (by omega)
  have v0 := h.out t ht
  have hl := h.len
  apply WP.of_runBlock
  simp (config := {decide := true}) only [rbLoad, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, i0, v0, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨h.flags (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, ?_, ?_, ?_⟩
  · refine eq_ofNat_of_toNat ?_
    rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide), toNat_byte32]
  · exact eq_ofNat_of_toNat (toNat_byte32 _)
  · simp only [eval, h.ecx, toNat_ofNat32 (show (LA s₀ t).length < 2 ^ 32 by omega)]
    rfl

theorem hi_ok {s₀ : State} {t : Nat} {La : List Zq} {s : State} (h : Loop s₀ t La s)
    (hax : s.gpr .eax = BitVec.ofNat 32 (zb s₀ t).toNat) :
    WP isa (.block rbHi) s fun s' => Loop s₀ t La s' ∧ s'.gpr .edx = BitVec.ofNat 32 (hi s₀ t) ∧
      s'.gpr .eax = BitVec.ofNat 32 (hi s₀ t) ∧ eval .b s' = some (decide (La.length < 256)) := by
  have hl := h.len
  have hz := (zb s₀ t).isLt
  have hv : s.gpr .eax >>> 4 = BitVec.ofNat 32 (hi s₀ t) := by
    rw [hax]; exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (by omega)])
  apply WP.of_runBlock
  simp (config := {decide := true}) only [rbHi, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, hv,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨h.flags (by simp) (by simp) (by simp) (by simp) (by simp) rfl rfl rfl, by simp, by simp, ?_⟩
  simp only [eval, h.ecx, toNat_ofNat32 (show La.length < 2 ^ 32 by omega)]
  rfl

theorem end_ok {s₀ : State} {t : Nat} (ht : t < 544) {La : List Zq} {s : State} (h : Loop s₀ t La s) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .sub .ebp (.imm 1)]) s
      fun s' => Loop s₀ (t + 1) La s' ∧ eval .ne s' = some (decide (t + 1 < 544)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, h.len, by simp [h.edi], by simp [h.ecx],
    h.stored⟩, ?_⟩
  · simp only [ite_true, h.esi]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    exact cnt_next ht
  · simp only [eval, h.ebp]
    exact cnt_ne ht (by omega)

theorem body_piece {e : Nat} (he : e = 2 ∨ e = 4) (t : Nat) (ht : t < 544)
    (tc : TaintOk [] (.block [.alu .cmp .edx (.imm (rbBound e))]))
    (ts : TaintOk [.edi] (.block (rbVal e ++ stBlk))) :
    Piece BPre BPub (fun s₀ s => Loop s₀ t (LA s₀ t) s ∧ η s₀ = e)
      (fun s₀ s => (Loop s₀ (t + 1) (LA s₀ (t + 1)) s ∧ η s₀ = e) ∧ eval .ne s = some (decide (t + 1 < 544)))
      (rbBody e) := by
  refine Piece.seq (B := fun s₀ s => (Loop s₀ t (LA s₀ t) s ∧ s.gpr .edx = BitVec.ofNat 32 (lo s₀ t) ∧
      s.gpr .eax = BitVec.ofNat 32 (zb s₀ t).toNat ∧ eval .b s = some (decide ((LA s₀ t).length < 256))) ∧
      η s₀ = e) ?_ (Piece.seq (B := fun s₀ s => Loop s₀ t (LA s₀ (t + 1)) s ∧ η s₀ = e) ?_
        (Piece.taint [] (fun s₀ s _ ⟨h, hη⟩ => (end_ok ht h).mono fun s' ⟨h', hc⟩ => ⟨⟨h', hη⟩, hc⟩)
          (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)))
  · refine Piece.taint [.esi] (fun s₀ s hp ⟨h, hη⟩ => (load_ok hp ht h).mono fun s' h' => ⟨h', hη⟩)
      (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by taint_decide)
    simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esi, h'.esi, hq.1.sP hL]
  refine Piece.ite (fun s₀ => decide ((LA s₀ t).length < 256)) (fun _ _ _ h => h.1.2.2.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.LA_len t]) ?_ ?_
  · -- the low half-byte, then the high one
    refine Piece.seq ((try_piece he t (fun s₀ => LA s₀ t) (fun s₀ => lo s₀ t) (fun s₀ => (zb s₀ t).toNat)
      (fun s₀ => (LA s₀ t).length < 256) (fun s₀ s₀' h₀ _ hq => ⟨hq.LA_len t, lo_pub h₀ hq ht⟩) tc ts).mono
        (fun s₀ s _ ⟨⟨⟨h, hdx, hax, _⟩, hη⟩, hb⟩ =>
          ⟨⟨⟨h, hdx, hax, of_decide_eq_true hb, Nat.mod_lt _ (by decide)⟩, hη⟩, of_decide_eq_true hb⟩)
        fun _ _ _ h => h) ?_
    refine Piece.seq (B := fun s₀ s => ((Loop s₀ t (L1 s₀ t) s ∧ s.gpr .edx = BitVec.ofNat 32 (hi s₀ t) ∧
        s.gpr .eax = BitVec.ofNat 32 (hi s₀ t) ∧ eval .b s = some (decide ((L1 s₀ t).length < 256))) ∧
        η s₀ = e) ∧ (LA s₀ t).length < 256)
      (Piece.taint [] (fun s₀ s _ ⟨⟨⟨h, hax⟩, hη⟩, hx⟩ => (hi_ok h hax).mono fun s' h' => ⟨⟨h', hη⟩, hx⟩)
        (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)) ?_
    refine Piece.ite (fun s₀ => decide ((L1 s₀ t).length < 256)) (fun _ _ _ h => h.1.1.2.2.2)
      (fun s₀ s₀' _ _ hq => by rw [L1_len hq ht]) ?_ ?_
    · refine (try_piece he t (fun s₀ => L1 s₀ t) (fun s₀ => hi s₀ t) (fun s₀ => hi s₀ t)
        (fun s₀ => (LA s₀ t).length < 256 ∧ (L1 s₀ t).length < 256)
        (fun s₀ s₀' h₀ _ hq => ⟨L1_len hq ht, hi_pub h₀ hq ht⟩) tc ts).mono
          (fun s₀ s _ ⟨⟨⟨⟨h, hdx, hax, _⟩, hη⟩, hx⟩, hb⟩ =>
            ⟨⟨⟨h, hdx, hax, of_decide_eq_true hb,
              show (zb s₀ t).toNat / 16 < 16 by have := (zb s₀ t).isLt; omega⟩, hη⟩, hx, of_decide_eq_true hb⟩) ?_
      rintro s₀ s _ ⟨⟨⟨h, -⟩, hη⟩, hx, hx'⟩
      refine ⟨?_, hη⟩
      rw [LA_step ht, ifT hx, ifT hx']; exact h
    · exact nil_piece fun s₀ s _ ⟨⟨⟨⟨h, _⟩, hη⟩, hx⟩, hb⟩ => by
        refine ⟨?_, hη⟩
        rw [LA_step ht, ifT hx, ifF (of_decide_eq_false hb)]; exact h
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, hη⟩, hb⟩ => by
      refine ⟨?_, hη⟩
      rw [LA_step ht, ifF (of_decide_eq_false hb)]; exact h

theorem loop_piece {e : Nat} (he : e = 2 ∨ e = 4)
    (tc : TaintOk [] (.block [.alu .cmp .edx (.imm (rbBound e))]))
    (ts : TaintOk [.edi] (.block (rbVal e ++ stBlk))) :
    Piece BPre BPub (fun s₀ s => Loop s₀ 0 (LA s₀ 0) s ∧ η s₀ = e)
      (fun s₀ s => Loop s₀ 544 (LA s₀ 544) s ∧ η s₀ = e) (.loop (rbBody e) .ne) :=
  Piece.loop (fun t s₀ s => Loop s₀ t (LA s₀ t) s ∧ η s₀ = e) (by decide) fun t ht => body_piece he t ht tc ts

/-- Before the branch on `η`: `edi = a`, and whether `η = 2` in ZF. -/
def Sel (s₀ s : State) : Prop :=
  Out L s₀ s ∧ s.gpr .edi = L.aP s₀ ∧ eval .e s = some (decide (η s₀ = 2))

theorem sel_piece : Piece BPre BPub (Out L) Sel
    (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 2)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp.1 (i := 1) (by decide)
    have v₁ := h.args 1 (by decide)
    have a₂ := h.argEa (i := 2)
    have i₂ := h.argIn hp.1 (i := 2) (by decide)
    have v₂ := h.args 2 (by decide)
    simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
    apply WP.of_runBlock
    simp (config := {decide := true}) only [argOp, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₁, i₁, v₁, a₂, i₂, v₂, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.out⟩, by simp; rfl, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.1.e1]

theorem init_piece (e : Nat) (b : Bool) (hb : ∀ s₀, BPre s₀ → decide (η s₀ = 2) = b → η s₀ = e) :
    Piece BPre BPub (fun s₀ s => Sel s₀ s ∧ decide (η s₀ = 2) = b) (fun s₀ s => Loop s₀ 0 (LA s₀ 0) s ∧ η s₀ = e)
    (.block [.alu .add .esi (.imm (BitVec.ofNat 32 840)), .mov .ecx (.imm 0), .mov .ebp (.imm 544)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨h, hdi, _⟩, e⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [LA_zero]
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, fun p hp' => ?_, by simp [h.esi], by simp, by simp,
    by simp [hdi], by simp, stored_nil _ _⟩, hb s₀ hp e⟩
  exact h.out p hp'

theorem branch_piece : Piece BPre BPub Sel (fun s₀ s => Loop s₀ 544 (LA s₀ 544) s)
    (.ite .e (rbLoop 2) (rbLoop 4)) := by
  refine Piece.ite (fun s₀ => decide (η s₀ = 2)) (fun _ _ _ h => h.2.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eη]) ?_ ?_
  · exact (Piece.seq (init_piece 2 true fun s₀ _ e => of_decide_eq_true e)
      (loop_piece (Or.inl rfl) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)).mono (fun _ _ _ h => h)
      fun _ _ _ h => h.1
  · exact (Piece.seq (init_piece 4 false fun s₀ hp e => hp.2.resolve_left (of_decide_eq_false e))
      (loop_piece (Or.inr rfl) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)).mono (fun _ _ _ h => h)
      fun _ _ _ h => h.1

/-- The end: 1 in `eax` if there are 256 coefficients, 0 if fewer. -/
structure Fin (s₀ s : State) : Prop extends Loop s₀ 544 (LA s₀ 544) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((LA s₀ 544).length / 256)

theorem fin_piece : Piece BPre BPub (fun s₀ s => Loop s₀ 544 (LA s₀ 544) s) Fin (.block (retJ .ecx)) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr,
    by rw [o.mem]; exact h.frame⟩, by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi],
    by rw [g _ (by decide), h.ebp], h.len, by rw [g _ (by decide), h.edi], by rw [g _ (by decide), h.ecx],
    by rw [o.mem]; exact h.stored⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.ecx]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (LA s₀ 544).length < 2 ^ 32 by omega)])

end VG.Proof.MlDsa.X86.Sample.RejBounded

namespace VG.Proof.MlDsa.X86.Sample.RejBounded

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp rbLoop retJ sponge)
open VG.Spec.MlDsa (Zq H)

/-! ## The whole function -/

theorem main_piece : Piece BPre BPub (fun s₀ s => s = P0 s₀) Fin
    (.seq (sponge 3 136 (.imm 66) 544)
      (.seq (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 2)])
        (.seq (.ite .e (rbLoop 2) (rbLoop 4)) (.block (retJ .ecx))))) :=
  Piece.seq ((sponge_piece hL).pre_mono (fun _ h => h.1) fun _ _ _ _ h => h.1) <|
    Piece.seq sel_piece <| Piece.seq branch_piece fin_piece

theorem piece : Piece BPre BPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.rejBounded :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨by have := hp.1.sp; omega, by have := hp.1.sp'; omega⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem BPre.of {s₀ : State} (h : (Spec.MlDsa.rejBoundedContract X86.abi 56).pre s₀) : BPre s₀ := by
  sig_pre [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    show (66 : Nat) < 136 by decide⟩, h22⟩

theorem LA_all (s₀ : State) : LA s₀ 544 = rbFold (η s₀) [] (H (L.Msg s₀) 544) := by
  simp only [LA]; rw [List.take_of_length_le (by rw [X_length]), X_eq]

/-- Memory with the arguments `0`, `2`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 2 else if a = 0x500d then 1 else if a = 0x5011 then 0x10 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Sample.rejBounded (Spec.MlDsa.rejBoundedContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => BPre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
    refine ⟨⟨e₁, fun i hi => ?_⟩, e₂⟩
    match i, hi with
    | 0, _ => exact e₃
    | 1, _ => exact e₄
    | 2, _ => exact e₅
    | 3, _ => exact e₆
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl := hfin.len
    by_cases e : (LA s₀ 544).length = 256
    · have hp : Spec.MlDsa.PolyIs s.mem (L.aA s₀) (toPoly (LA s₀ 544)) := stored_polyIs hfin.stored e
      rw [LA_all] at e hp
      rw [LA_all, e]
      refine ⟨fun _ => hp.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, ?_⟩⟩
      show (Spec.MlDsa.rejBoundedPoly (η s₀) 544 (L.Msg s₀)).map Spec.MlDsa.toRq =
        some (Spec.MlDsa.polyAt s.mem (L.aA s₀))
      rw [rejBounded_some _ e, hp.2]
    · rw [Nat.div_eq_of_lt (by omega)]
      rw [LA_all] at e
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide),
        .inr ⟨rfl, ?_⟩⟩
      show (Spec.MlDsa.rejBoundedPoly (η s₀) Spec.MlDsa.minBounds.rejBounded (L.Msg s₀)).map Spec.MlDsa.toRq = none
      rw [rejBounded_none _ (B := 544) (by decide) e]; rfl
  · let st := satState satMem [⟨0, 66⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlDsa.rejBoundedContract, Spec.MlDsa.rejBoundedSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.RejBounded
