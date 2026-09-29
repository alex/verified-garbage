import VerifiedGarbage.Proof.MlKem.X86.Top
import VerifiedGarbage.Proof.MlKem.X86.CallRet
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): calls in the top-level functions

Untrusted: everything here is checked by Lean. `call_piece` makes a call of
verified code from a state satisfying `Ctx`, in a frame of its arguments,
as a `Piece`: the callee's precondition (`CallPre`), its public data, and
the regions it writes (within `W`) are what remains to prove, and `Ctx`
holds after it. The calls of the Keccak functions (`absorb_call`,
`pad_call`, `squeeze_call`) are made with their buffers named as `Buf`s.

The callee sees the stack below `esp = E` as its arguments (`below E (4k)`),
its return address, and its own stack below that (`entry_regions`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- A call of verified code, from `Ctx`. -/
theorem call_piece {k : Contract isa} {rs : List Reg} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c k) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (hN : 4 * rs.length + stackUse c + 4 + 16 ≤ Y.stk) (rd wr : State → List Region)
    (hk : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, TPre Y s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ W Y s₀, Region.Sub r r')
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (E1 s₀) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith rs nm c) :=
  Piece.callWith hv.1 hv.2.1 hsp hne hrs rd wr
    (fun s₀ s hp ha => by rw [(hk s₀ s hp ha).1.esp, E1_nat s₀ hp.E0_big]; have := hp.sp; omega)
    (fun s₀ s hp ha => (hk s₀ s hp ha).2)
    (fun s₀ s₀' s s' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s s' hp hp' hq ha ha'
      exact ⟨e₁, e₂, by rw [(hk _ _ hp ha).1.esp, (hk _ _ hp' ha').1.esp, hq.E1], e₃⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => by
      have h := (hk s₀ s hp ha).1
      rw [h.esp] at fr
      refine hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) e₃ fr post
      rcases List.mem_append.mp hr with hr | hr
      · exact hW s₀ hp r hr
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨cR Y s₀, TPre.cW, below_sub (by omega) (by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega)⟩)

/-- `call_piece`, for `callRet`: the value the callee returns stays in `eax`. -/
theorem callR_piece {k : Contract isa} {rs : List Reg} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c k) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (hN : 4 * rs.length + stackUse c + 4 + 16 ≤ Y.stk) (rd wr : State → List Region)
    (hk : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, TPre Y s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ W Y s₀, Region.Sub r r')
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (E1 s₀) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callRet rs nm c) :=
  Piece.callRet hv.1 hv.2.1 hsp hne hrs rd wr
    (fun s₀ s hp ha => by rw [(hk s₀ s hp ha).1.esp, E1_nat s₀ hp.E0_big]; have := hp.sp; omega)
    (fun s₀ s hp ha => (hk s₀ s hp ha).2)
    (fun s₀ s₀' s s' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s s' hp hp' hq ha ha'
      exact ⟨e₁, e₂, by rw [(hk _ _ hp ha).1.esp, (hk _ _ hp' ha').1.esp, hq.E1], e₃⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => by
      have h := (hk s₀ s hp ha).1
      rw [h.esp] at fr
      refine hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) e₃ fr post
      rcases List.mem_append.mp hr with hr | hr
      · exact hW s₀ hp r hr
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨cR Y s₀, TPre.cW, below_sub (by omega) (by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega)⟩)

/-! ## The callee's view of the stack -/

theorem entry_regions {E : BitVec 32} {k K : Nat} (hE : 4 * k + 4 + K ≤ E.toNat) {R : Region}
    (hR : (below E (4 * k + 4 + K)).Disjoint R) :
    R.Disjoint (below E (4 * k)) ∧
      (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ : Region).Disjoint R ∧
      (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint R := by
  have hr : Region.Sub ⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ (below E (4 * k + 4 + K)) := by
    have := below_inner (sp := E) (a := 4) (b := 4 * k + 4 + K) (k := 4 * k) (by omega) hE
    have e : (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ : Region) = below (E - BitVec.ofNat 32 (4 * k)) 4 := by
      simp only [below]; congr 2; rw [BitVec.ofNat_add]; bv_omega
    rw [e]; exact this
  have hs : Region.Sub ⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩
      (below E (4 * k + 4 + K)) := by
    have := below_inner (sp := E) (a := K) (b := 4 * k + 4 + K) (k := 4 * k + 4) (by omega) hE
    have e : (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region) =
        below (E - BitVec.ofNat 32 (4 * k + 4)) K := by
      simp only [below]
      rw [Taint.sub_setWidth (show K ≤ (E - BitVec.ofNat 32 (4 * k + 4)).toNat by rw [sub_toNat (by omega)]; omega)]
    rw [e]; exact this
  exact ⟨(hR.sub_left (below_sub (by omega) hE)).symm, hR.sub_left hr, hR.sub_left hs⟩

theorem entry_self {E : BitVec 32} {k K : Nat} (hE : 4 * k + 4 + K ≤ E.toNat) :
    (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ : Region).Disjoint (below E (4 * k)) ∧
      (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint
        (below E (4 * k)) := by
  constructor
  · intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [Taint.sub_setWidth (by omega)] at h₁
    rw [Taint.sub_setWidth (by omega)] at h₂
    have := E.isLt
    have hE' : (E.setWidth 64).toNat = E.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    generalize E.setWidth 64 = X at *
    bv_omega
  · intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [Taint.sub_setWidth (by omega)] at h₁
    rw [Taint.sub_setWidth (by omega)] at h₂
    have := E.isLt
    have hE' : (E.setWidth 64).toNat = E.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    generalize E.setWidth 64 = X at *
    bv_omega

/-- The callee's regions, within the caller's. -/
theorem covers_of {s : State} {n : Nat} {rd wr : List Region}
    (hrd : ∀ r ∈ rd, Within r (s.rd ++ s.wr))
    (hwr : ∀ r ∈ wr, r = below (s.gpr .esp) (4 * n) ∨ Within r s.wr) :
    Covers (rd ++ wr) (s.rd ++ below (s.gpr .esp) (4 * n) :: s.wr) ∧
      Covers wr (below (s.gpr .esp) (4 * n) :: s.wr) := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', h', o, hb, hl⟩ := hrd r hr
      refine ⟨r', ?_, o, hb, hl⟩
      rcases List.mem_append.mp h' with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
    · rcases hwr r hr with rfl | ⟨r', h', o, hb, hl⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), 0, by simp, by simp⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h'), o, hb, hl⟩
  · rcases hwr r hr with rfl | ⟨r', h', o, hb, hl⟩
    · exact ⟨_, List.mem_cons_self .., 0, by simp, by simp⟩
    · exact ⟨r', List.mem_cons_of_mem _ h', o, hb, hl⟩

theorem ctx_E {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {N : Nat} (hN : N + 16 ≤ Y.stk) :
    N ≤ (s.gpr .esp).toNat := by
  rw [h.esp, E1_nat s₀ hp.E0_big]; have := hp.sp; omega

theorem stk_sub {s₀ : State} (hp : TPre Y s₀) {a b : Nat} (hab : a ≤ b) (hN : b + 16 ≤ Y.stk) :
    Region.Sub (below (E1 s₀) a) (below (E1 s₀) b) :=
  below_sub hab (by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega)

/-! ## The Keccak functions -/

/-- A call of `vg_keccak_absorb`, with the state at `(sa, so)`, the data `bD` and the working space at
`(wa, wo)`. -/
theorem absorb_call (sa so wa wo : Nat) (bD : Buf) (rate pos : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨sa, so, 200⟩ && Y.okW ⟨wa, wo, 640⟩ && Y.ok bD && Y.sep ⟨sa, so, 200⟩ ⟨wa, wo, 640⟩ &&
      Y.sep bD ⟨sa, so, 200⟩ && Y.sep bD ⟨wa, wo, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : bD.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧
      AbsArgs s (Buf.ptr s₀ ⟨sa, so, 200⟩) (bD.ptr s₀) (Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bD.len)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨sa, so, 200⟩, ⟨wa, wo, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨sa, so, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨sa, so, 200⟩) rate (msg ++ bytesAt s.mem (bD.addr s₀) bD.len)) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith rs6 "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hS, hW⟩, hD⟩, dSW⟩, dDS⟩, dDW⟩ := hc
  have hS' := (Lay.okW_iff.mp hS).1
  have hW' := (Lay.okW_iff.mp hW).1
  refine absorb_piece (fun s₀ => E1 s₀) (fun s₀ => Buf.ptr s₀ ⟨sa, so, 200⟩) (fun s₀ => bD.ptr s₀)
    (fun s₀ => Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bD.len hr hpos hlen (fun s₀ s hp ha => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, hq.ptr hS', hq.ptr hD, hq.ptr hW'⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨h, ha⟩ := hA s₀ s hp ha
    have hE : 40 ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
    exact ⟨h.esp, ha, ⟨hE, Buf.fit hp hS', Buf.fit hp hW', Buf.disj hp hS' hW' dSW,
      Buf.stkD hp hS' (by omega), Buf.stkD hp hW' (by omega)⟩, Buf.fit hp hD, Buf.disj hp hD hS' dDS,
      Buf.disj hp hD hW' dDW, Buf.stkD hp hD (by omega), Buf.within hp hD h.rd h.wr,
      Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr, Buf.withinW hp hW' (Lay.okW_iff.mp hW).2 h.wr⟩
  · have h := (hA s₀ s hp ha).1
    exact hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr (Buf.frSub hp (bs := [⟨sa, so, 200⟩, ⟨wa, wo, 640⟩])
      (by simp [hS, hW]) (by omega))) e₃ fr post

/-- A call of `vg_keccak_pad`. -/
theorem pad_call (sa so wa wo : Nat) (rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨sa, so, 200⟩ && Y.okW ⟨wa, wo, 640⟩ && Y.sep ⟨sa, so, 200⟩ ⟨wa, wo, 640⟩) = true)
    (hN : 56 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧
      PadArgs s (Buf.ptr s₀ ⟨sa, so, 200⟩) (Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos sfx)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨sa, so, 200⟩, ⟨wa, wo, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨sa, so, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨sa, so, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith rs5 "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hS, hW⟩, dSW⟩ := hc
  have hS' := (Lay.okW_iff.mp hS).1
  have hW' := (Lay.okW_iff.mp hW).1
  refine pad_piece (fun s₀ => E1 s₀) (fun s₀ => Buf.ptr s₀ ⟨sa, so, 200⟩) (fun s₀ => Buf.ptr s₀ ⟨wa, wo, 640⟩)
    rate pos sfx hr hpos (fun s₀ s hp ha => ?_) (fun s₀ s₀' _ _ hq => ⟨hq.E1, hq.ptr hS', hq.ptr hW'⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨h, ha⟩ := hA s₀ s hp ha
    have hE : 40 ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
    exact ⟨h.esp, ha, ⟨hE, Buf.fit hp hS', Buf.fit hp hW', Buf.disj hp hS' hW' dSW,
      Buf.stkD hp hS' (by omega), Buf.stkD hp hW' (by omega)⟩,
      Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr, Buf.withinW hp hW' (Lay.okW_iff.mp hW).2 h.wr⟩
  · have h := (hA s₀ s hp ha).1
    exact hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr (Buf.frSub hp (bs := [⟨sa, so, 200⟩, ⟨wa, wo, 640⟩])
      (by simp [hS, hW]) (by omega))) e₃ fr post

/-- A call of `vg_keccak_squeeze`, into `bO`. -/
theorem squeeze_call (sa so wa wo : Nat) (bO : Buf) (rate pos : Nat) (hr : rate ∈ rates) (hpos : pos ≤ rate)
    (hc : (Y.okW ⟨sa, so, 200⟩ && Y.okW ⟨wa, wo, 640⟩ && Y.okW bO && Y.sep ⟨sa, so, 200⟩ ⟨wa, wo, 640⟩ &&
      Y.sep ⟨sa, so, 200⟩ bO && Y.sep bO ⟨wa, wo, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : bO.len < 2 ^ 32)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧
      AbsArgs s (Buf.ptr s₀ ⟨sa, so, 200⟩) (bO.ptr s₀) (Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bO.len)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨sa, so, 200⟩, bO, ⟨wa, wo, 640⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (bO.addr s₀) bO.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨sa, so, 200⟩)) pos bO.len →
      (∃ pos' ≤ rate, ∀ d, squeezeFrom rate (stateAt s'.mem (Buf.addr s₀ ⟨sa, so, 200⟩)) pos' d =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨sa, so, 200⟩)) (pos + bO.len) d) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith rs6 "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hS, hW⟩, hO⟩, dSW⟩, dSO⟩, dOW⟩ := hc
  have hS' := (Lay.okW_iff.mp hS).1
  have hW' := (Lay.okW_iff.mp hW).1
  have hO' := (Lay.okW_iff.mp hO).1
  refine squeeze_piece (fun s₀ => E1 s₀) (fun s₀ => Buf.ptr s₀ ⟨sa, so, 200⟩) (fun s₀ => bO.ptr s₀)
    (fun s₀ => Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bO.len hr hpos hlen (fun s₀ s hp ha => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, hq.ptr hS', hq.ptr hO', hq.ptr hW'⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr r₁ r₂ => ?_)
  · obtain ⟨h, ha⟩ := hA s₀ s hp ha
    have hE : 40 ≤ (E1 s₀).toNat := by rw [E1_nat s₀ hp.E0_big]; have := hp.sp; omega
    exact ⟨h.esp, ha, ⟨hE, Buf.fit hp hS', Buf.fit hp hW', Buf.disj hp hS' hW' dSW,
      Buf.stkD hp hS' (by omega), Buf.stkD hp hW' (by omega)⟩, Buf.fit hp hO', Buf.disj hp hS' hO' dSO,
      Buf.disj hp hO' hW' dOW, Buf.stkD hp hO' (by omega),
      Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr, Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr,
      Buf.withinW hp hW' (Lay.okW_iff.mp hW).2 h.wr⟩
  · have h := (hA s₀ s hp ha).1
    exact hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr (Buf.frSub hp (bs := [⟨sa, so, 200⟩, bO, ⟨wa, wo, 640⟩])
      (by simp [hS, hW, hO]) (by omega))) e₃ fr r₁ r₂

/-! ## Helpers for the primitives -/

/-- The regions a call writes: its buffers and its arguments' frame, within `W`. -/
theorem wr_sub {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} (hbs : bs.all Y.okW = true) {a : Nat}
    (ha : a + 16 ≤ Y.stk) : ∀ r ∈ bs.map (Buf.rgn s₀) ++ [below (E1 s₀) a], ∃ r' ∈ W Y s₀, Region.Sub r r' :=
  Buf.frSub hp hbs ha

/-- The frame a call leaves: its buffers, and the stack it uses. -/
theorem fr_conv {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {a N : Nat} (ha : a ≤ N) (hN : N + 16 ≤ Y.stk)
    {m m' : Mem} (fr : Frame (bs.map (Buf.rgn s₀) ++ [below (E1 s₀) a] ++ [below (E1 s₀) N]) m m') :
    Frame (bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N]) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨below (E1 s₀) N, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp ha hN⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨below (E1 s₀) N, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩

/-- The bytes of a buffer, as the callee sees them. -/
theorem ent_keep {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {rs : List Reg} (hrs : Reg.esp ∉ rs)
    (fit : 4 * rs.length + 4 + 16 ≤ Y.stk) {b : Buf} (hb : Y.ok b = true) :
    ∀ i < b.len, (pushed rs s).callEntry.mem (b.addr s₀ + BitVec.ofNat 64 i) = s.mem (b.addr s₀ + BitVec.ofNat 64 i) :=
  fun _ hi => (callEntry_frame (ctx_E hp h (N := 4 * rs.length + 4) (by omega)) hrs).bytes (R := b.rgn s₀)
    (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
      exact (Buf.stkD hp hb (N := 4 * rs.length + 4) (by omega)).symm)
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi

end VG.Proof.MlKem.X86.Top
