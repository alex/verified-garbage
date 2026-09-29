import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.X86.Cbd
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_cbd2`

Untrusted: everything here is checked by Lean. Byte `k` holds the nibbles of
coefficients `2k` and `2k+1` (`samplePolyCBD2_val`); `cbdNibble` computes
`x + q - y` of a nibble with masks and shifts (`nib_spec`) and reduces it.
-/

namespace VG.Proof.MlKem.X86.Cbd

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## A nibble -/

theorem land5 (m : Nat) : m &&& 5 = m % 2 + 4 * (m / 4 % 2) := by
  have h : m &&& 5 = (m % 8) &&& 5 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod m 3, Nat.and_assoc]; rfl
  have key : ∀ r < 8, r &&& 5 = r % 2 + 4 * (r / 4 % 2) := by decide
  rw [h, key _ (Nat.mod_lt _ (by decide))]
  omega

/-- The sum `t` of the two masked halves, as numbers. -/
theorem cbd_t (v : BitVec 32) :
    ((v &&& (5 : BitVec 32)) + (v >>> 1 &&& (5 : BitVec 32))).toNat =
      v.toNat % 2 + 4 * (v.toNat / 4 % 2) + (v.toNat / 2 % 2 + 4 * (v.toNat / 8 % 2)) := by
  have a1 : (v &&& (5 : BitVec 32)).toNat = v.toNat % 2 + 4 * (v.toNat / 4 % 2) := by
    rw [BitVec.toNat_and, ← land5]; rfl
  have a2 : (v >>> 1 &&& (5 : BitVec 32)).toNat = v.toNat / 2 % 2 + 4 * (v.toNat / 8 % 2) := by
    rw [BitVec.toNat_and, show (v >>> 1).toNat &&& (5 : BitVec 32).toNat = (v >>> 1).toNat &&& 5 from rfl,
      land5, toNat_shr]
    omega
  rw [BitVec.toNat_add, a1, a2]
  omega

/-- `cbdNibble` computes `(x + q - y) mod q` of the nibble in `eax`, changing only `eax`, `edx`
and the flags. -/
theorem nib_spec (is : List Instr) (s : State) (P : State → Prop)
    (k : ∀ s', Only [.eax, .edx] s s' →
      s'.gpr .eax = BitVec.ofNat 32 ((cbdX (s.gpr .eax).toNat + q - cbdY (s.gpr .eax).toNat) % q) →
      WP isa (.block is) s' P) :
    WP isa (.block (cbdNibble ++ is)) s P := by
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [cbdNibble, csub, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, execShift, readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.map_some, ite_true, ite_false, Option.some.injEq, exists_eq_left', List.cons_append,
    List.nil_append]
  refine k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · simp only [ite_true]
    generalize s.gpr .eax = v
    have ht := cbd_t v
    generalize (v &&& (5 : BitVec 32)) + (v >>> 1 &&& (5 : BitVec 32)) = t at ht
    have hx : (t &&& (3 : BitVec 32)).toNat = cbdX v.toNat := by
      rw [show (3 : BitVec 32) = BitVec.ofNat 32 (2 ^ 2 - 1) from rfl, toNat_and_mask _ _ (by decide),
        ht, cbdX]
      omega
    have hy : (t >>> 2).toNat = cbdY v.toNat := by
      rw [toNat_shr, ht, cbdY]; omega
    have hxl := cbdX_le v.toNat
    have hyl := cbdY_le v.toNat
    have e : ((t &&& (3 : BitVec 32)) + Q - t >>> 2).toNat = cbdX v.toNat + q - cbdY v.toNat := by
      have hQ : ((t &&& (3 : BitVec 32)) + Q).toNat = cbdX v.toNat + 3329 := by
        rw [BitVec.toNat_add, hx, show Q.toNat = 3329 from rfl, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, hy]; omega), hQ, hy, q_eq]
    rw [csub_eq _ _ (by rw [e, q_eq]; omega), e]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev bP : BitVec 32 := arg s₀ 0
abbrev fP : BitVec 32 := arg s₀ 1
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, 128⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 4 * 2⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The input bytes. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) 128
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * 2 ≤ 2 ^ 32
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [polyRegion (fA s₀), aR s₀]
  b_f : (bR s₀).Disjoint (polyRegion (fA s₀))
  b_a : (bR s₀).Disjoint (aR s₀)
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  ret_b : (retR s₀).Disjoint (bR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_b : (stkR s₀).Disjoint (bR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  b_fit : (bP s₀).toNat + 128 ≤ 2 ^ 32
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32

theorem Pre.of {s₀ : State} (h : (cbd2Contract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The value of coefficient `i`. -/
abbrev V (s₀ : State) (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((samplePolyCBD 2 (B s₀))[i]!).val

/-- After `k` bytes. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = bP s₀ + BitVec.ofNat 32 k
  edi : s.gpr .edi = fP s₀ + BitVec.ofNat 32 (8 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (128 - k)
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 2 * k, coeffAt s.mem (fA s₀) i = V s₀ i

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem b_keep {s : State} (hf : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem) {j : Nat} (hj : j < 128) :
    s.mem (bA s₀ + BitVec.ofNat 64 j) = (B s₀).getD j 0 := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  have l : (bR s₀).len ≤ 2 ^ 64 := by show 128 ≤ 2 ^ 64; decide
  rw [bytesAt_getD _ _ hj, hf.bytes (R := bR s₀) (by simpa using hp.b_f) l hj,
    hf₁.bytes (R := bR s₀) (by simpa [← hp.stk_eq] using hp.stk_b.symm) l hj]

end Pre

theorem init_piece :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) (Inv · 0) (.block cbdInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₁ := P0_argAddr s₀ 1
    have i₀ := P0_argIn (s₀ := s₀) (n := 2) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₁ := P0_argIn (s₀ := s₀) (n := 2) (i := 1) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 2) (i := 0) (by omega) fit hp.stk_a
    have v₁ := P0_arg hp.sp (n := 2) (i := 1) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    apply WP.of_runBlock
    simp (config := {decide := true}) only [cbdInit, at_, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀,
      i₁, v₀, v₁, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, rfl, rfl, by simp, by simp, by simp, Frame.refl _ _, fun j hj => absurd hj (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-- Coefficient `2k + e` from the nibble `e` of byte `k`. -/
theorem V_eq (s₀ : State) {k : Nat} (hk : k < 128) {e : Nat} (he : e < 2) :
    V s₀ (2 * k + e) = BitVec.ofNat 32 ((cbdX (((B s₀).getD k 0).toNat / 16 ^ e) + q -
      cbdY (((B s₀).getD k 0).toNat / 16 ^ e)) % q) := by
  rw [V, samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble,
    show (2 * k + e) / 2 = k by omega, show (2 * k + e) % 2 = e by omega]

theorem step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : Inv s₀ k s) :
    WP isa (.block cbdBody) s fun s' => Inv s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 128)) := by
  have fb := hp.b_fit
  have ff := hp.f_fit
  have eb : s.ea (at_ .esi 0) = bA s₀ + BitVec.ofNat 64 k := by
    show (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _
    rw [h.esi, ea_add (by omega), Nat.add_zero]
  have inB : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 1 :=
    ⟨bR s₀, by rw [h.rd, pushed_rd, hp.rd]; simp, by rw [eb]; exact contains_at (by omega) fb⟩
  have outF : ∀ i < 256, InRegions s.wr (coeffAddr (fA s₀) i) 4 := fun i hi =>
    ⟨polyRegion (fA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, coeff_contains _ hi⟩
  have o0 : (fP s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (fA s₀) (2 * k) := by rw [ea_add (by omega)]; congr 2; omega
  have o1 : (fP s₀ + BitVec.ofNat 32 (8 * k) + BitVec.ofNat 32 4).setWidth 64 =
      coeffAddr (fA s₀) (2 * k + 1) := by rw [ea_add (by omega)]; congr 2; omega
  have hbyte : s.mem (s.ea (at_ .esi 0)) = (B s₀).getD k 0 := by rw [eb, hp.b_keep h.frame hk]
  generalize eB : (B s₀).getD k 0 = b at hbyte
  refine wp_movzx inB (wp_movr ?_)
  rw [hbyte]
  set s₁ := (s.setReg .ebx (b.setWidth 32)).setReg .eax ((s.setReg .ebx (b.setWidth 32)).gpr .ebx)
    with hs₁
  have g₁ : ∀ r, r ≠ .eax → r ≠ .ebx → s₁.gpr r = s.gpr r := fun r h1 h2 => by
    simp [hs₁, State.setReg, h1, h2]
  have bx₁ : s₁.gpr .ebx = b.setWidth 32 := by simp [hs₁, State.setReg]
  have ax₁ : s₁.gpr .eax = b.setWidth 32 := by simp [hs₁, State.setReg]
  refine nib_spec _ s₁ _ fun s₂ o₂ v₂ => ?_
  have in0 : InRegions s₂.wr (s₂.ea (at_ .edi 0)) 4 := by
    rw [State.ea, at_, o₂.gpr _ (by decide), g₁ _ (by decide) (by decide), h.edi, o0, o₂.wr]
    exact outF _ (by omega)
  refine wp_store in0 (wp_movr ?_)
  refine wp_shr (by decide) (by decide) fun s₃ o₃ v₃ => ?_
  refine nib_spec _ s₃ _ fun s₄ o₄ v₄ => ?_
  -- What `s₄` holds.
  have g₄ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₄.gpr r (by simp [h1, h2]), o₃.gpr r (by simp [h1])]
    simp only [State.setReg, h1, ite_false]
    rw [o₂.gpr r (by simp [h1, h2]), g₁ r h1 h3]
  have esi₄ : s₄.gpr .esi = bP s₀ + BitVec.ofNat 32 k := by rw [g₄ _ (by decide) (by decide) (by decide), h.esi]
  have edi₄ : s₄.gpr .edi = fP s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [g₄ _ (by decide) (by decide) (by decide), h.edi]
  have ecx₄ : s₄.gpr .ecx = BitVec.ofNat 32 (128 - k) := by rw [g₄ _ (by decide) (by decide) (by decide), h.ecx]
  have esp₄ : s₄.gpr .esp = s.gpr .esp := g₄ _ (by decide) (by decide) (by decide)
  have edi₂ : s₂.gpr .edi = fP s₀ + BitVec.ofNat 32 (8 * k) := by
    rw [o₂.gpr _ (by decide), g₁ _ (by decide) (by decide), h.edi]
  have mem₄ : s₄.mem = s.mem.writeW (coeffAddr (fA s₀) (2 * k)) (s₂.gpr .eax) := by
    rw [o₄.mem, o₃.mem]
    simp only [State.ea, at_, edi₂, o0, o₂.mem]
    rfl
  have wr₄ : s₄.wr = s.wr := by rw [o₄.wr, o₃.wr, o₂.wr]; rfl
  have rd₄ : s₄.rd = s.rd := by rw [o₄.rd, o₃.rd, o₂.rd]; rfl
  have ax₃ : s₃.gpr .eax = b.setWidth 32 >>> 4 := by
    rw [v₃]; simp only [State.setReg, ite_true]; rw [o₂.gpr _ (by decide), bx₁]
  have out1 : InRegions s₄.wr (coeffAddr (fA s₀) (2 * k + 1)) 4 := by rw [wr₄]; exact outF _ (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, edi₄, o1, out1,
    ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  have lb := b.isLt
  have c0 : s₂.gpr .eax = V s₀ (2 * k) := by
    rw [v₂, ax₁, toNat_byte32, ← eB]
    have := V_eq s₀ hk (e := 0) (by decide)
    rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at this
    rw [this]
  have c1 : s₄.gpr .eax = V s₀ (2 * k + 1) := by
    rw [v₄, ax₃, toNat_shr, toNat_byte32, ← eB, V_eq s₀ hk (e := 1) (by decide), Nat.pow_one]
  refine ⟨⟨by simp [esp₄, h.esp], rd₄.trans h.rd, wr₄.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true,
      esi₄]
    exact add_ofNat_add _ _ _
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, edi₄]
    exact ptr_next _ _ 8
  · simp only [ite_true, ecx₄]
    exact cnt_next hk
  · rw [mem₄]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by rw [n_eq]; omega))
  · rw [show 2 * (k + 1) = 2 * k + 2 by omega, mem₄, c0, c1]
    exact coef_extend2 (by omega) h.coef
  · simp only [eval, ecx₄]
    exact cnt_ne hk (by decide)

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Inv s₀ 128) s₀ s')
    Impl.MlKem.X86.cbd2 :=
  Piece.leafLoop (fun s₀ => [polyRegion (fA s₀)]) (fun k s₀ s => Inv s₀ k s)
    (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1) init_piece
    (Piece.countLoop (by decide) (fun k s₀ s => Inv s₀ k s) [.esp, .esi, .edi, .ecx]
      (fun _ hk _ _ hp h => step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, bP, bP, hq.2.1]
        · rw [h.edi, h'.edi, fP, fP, hq.2.2]
        · rw [h.ecx, h'.ecx]) (by taint_decide))
    fun _ _ _ h => ⟨h.frame, h.esp, h.rd, h.wr⟩

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.cbd2 (cbd2Contract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.coef i (by rw [n_eq] at hi; omega)
  · let st := satState satMem [⟨0, 128⟩] [⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    have esp : st.gpr .esp = 0x5000 := rfl
    refine ⟨st, ?_⟩
    sig_pre [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, e, esp]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)
end VG.Proof.MlKem.X86.Cbd
