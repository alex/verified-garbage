import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem1024.X86.Pack
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_compress_encode`

The branch on `d` depends only on `d`; each branch is a loop over the 32
groups of 8 coefficients, packed with `accSs` (`Pack.lean`) into words whose
bytes are those of `compressEncode5_*` and `compressEncode11_*`
(`Encode1024.lean`), stored by `st4` and `st3` (`st4_spec`, `st3_spec`). `G b
t k` is the state within group `t` of `b` bytes, after its first `k` bytes.
-/

namespace VG.Proof.MlKem1024.X86.CompressEncode

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem1024.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev dV : BitVec 32 := arg s₀ 1
abbrev oP : BitVec 32 := arg s₀ 2
abbrev lenV : BitVec 32 := arg s₀ 3
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev oA : Addr := (oP s₀).setWidth 64
abbrev oR : Region := ⟨oA s₀, (lenV s₀).toNat⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev dN : Nat := (dV s₀).toNat
/-- The input polynomial. -/
abbrev F : Poly := polyAt s₀.mem (fA s₀)
/-- The encoding. -/
abbrev L : List Byte := compressEncode (dN s₀) (F s₀)
/-- Compressed coefficient `i`. -/
abbrev C (i : Nat) : Nat := compress (dN s₀) (F s₀)[i]!
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA s₀)]
  wr : s₀.wr = [oR s₀, aR s₀]
  f_o : (polyRegion (fA s₀)).Disjoint (oR s₀)
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  o_a : (oR s₀).Disjoint (aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_o : (retR s₀).Disjoint (oR s₀)
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_o : (stkR s₀).Disjoint (oR s₀)
  stk_a : (stkR s₀).Disjoint (aR s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + (lenV s₀).toNat ≤ 2 ^ 32
  d_mem : dN s₀ ∈ Spec.MlKem1024.compressWidths
  len_eq : (lenV s₀).toNat = 32 * dN s₀
  f_red : Reduced s₀.mem (fA s₀)

theorem Pre.of {s₀ : State} (h : (Spec.MlKem1024.compressEncodeContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem f_keep {s : State} (hf : Frame [oR s₀] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  refine coeffAt_congr (fun j hj => ?_) hi
  rw [hf.bytes (R := polyRegion (fA s₀)) (by simpa using hp.f_o) (polyLen _) hj,
    hf₁.bytes (R := polyRegion (fA s₀)) (by simpa [← hp.stk_eq] using hp.stk_f.symm) (polyLen _) hj]

/-- `C i` from what the coefficient holds in memory. -/
theorem C_eq {i : Nat} (hi : i < 256) :
    C s₀ i = cf (dN s₀) (coeffAt s₀.mem (fA s₀) i).toNat := by
  rw [cf_eq hp.d_mem (hp.f_red i hi), C, polyAt_get _ _ hi]

end Pre

/-- Within group `t` of `b` bytes, after its first `k` bytes, counting down from 32. -/
structure G (s₀ : State) (b t k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (32 * t)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (b * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (32 - t)
  frame : Frame [oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < b * t + k, s.mem (oA s₀ + BitVec.ofNat 64 j) = (L s₀)[j]!

/-- `G` holds of a state with the same memory, permissions and `esp`, `esi`, `edi` and `ecx`. -/
theorem G.of_regs {s₀ s s' : State} {b t k : Nat} (h : G s₀ b t k s) {ds : List Reg} (o : Regs ds s s')
    (hm : s'.mem = s.mem) (hd : Reg.esp ∉ ds ∧ Reg.esi ∉ ds ∧ Reg.edi ∉ ds ∧ Reg.ecx ∉ ds) : G s₀ b t k s' :=
  ⟨by rw [o.gpr _ hd.1, h.esp], by rw [o.rd, h.rd], by rw [o.wr, h.wr], by rw [o.gpr _ hd.2.1, h.esi],
    by rw [o.gpr _ hd.2.2.1, h.edi], by rw [o.gpr _ hd.2.2.2, h.ecx], hm ▸ h.frame, fun j hj => hm ▸ h.out j hj⟩

theorem G.of_only {s₀ s s' : State} {b t k : Nat} (h : G s₀ b t k s) {ds : List Reg} (o : Only ds s s')
    (hd : Reg.esp ∉ ds ∧ Reg.esi ∉ ds ∧ Reg.edi ∉ ds ∧ Reg.ecx ∉ ds) : G s₀ b t k s' :=
  h.of_regs (Regs.of_only o) o.mem hd

/-- The end of every branch. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [oR s₀] (P0 s₀).mem s.mem
  out : ∀ j < 32 * dN s₀, s.mem (oA s₀ + BitVec.ofNat 64 j) = (L s₀)[j]!

theorem G.fin {s₀ s : State} {b : Nat} (hb : dN s₀ = b) (h : G s₀ b 32 0 s) : Fin s₀ s :=
  ⟨h.esp, h.rd, h.wr, h.frame, fun j hj => h.out j (by rw [hb] at hj; omega)⟩

/-- Coefficient `8 t + i` of group `t`, read from `esi`. -/
theorem G.coef {s₀ s : State} (hp : Pre s₀) {b t k : Nat} (h : G s₀ b t k s) (ht : t < 32) {i : Nat}
    (hi : i < 8) : Coef s i (coeffAt s₀.mem (fA s₀) (8 * t + i)).toNat := by
  have ff := hp.f_fit
  have e : s.ea (at_ .esi (4 * i)) = coeffAddr (fA s₀) (8 * t + i) := by
    show (s.gpr .esi + BitVec.ofNat 32 (4 * i)).setWidth 64 = _
    rw [h.esi, ea_add (by omega)]
    congr 2; omega
  refine ⟨?_, ?_, hp.f_red _ (by rw [n_eq]; omega)⟩
  · rw [e]; exact ⟨polyRegion (fA s₀), by rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]; simp,
      coeff_contains _ (by rw [n_eq]; omega)⟩
  · rw [e, ← coeffAt_eq, hp.f_keep h.frame (by omega)]

/-- Coefficient `8 t + i` of group `t`, from `esi`, with an offset `o` of the index. -/
theorem G.coefO {s₀ s : State} (hp : Pre s₀) {b t k : Nat} (h : G s₀ b t k s) (ht : t < 32) (o : Nat)
    {i : Nat} (hi : o + i < 8) : Coef s (o + i) (coeffAt s₀.mem (fA s₀) (8 * t + (o + i))).toNat :=
  h.coef hp ht hi

/-- Store byte `k` of group `t` at `edi + k`. -/
theorem G.st8 {s₀ s : State} (hp : Pre s₀) {b t k : Nat} (h : G s₀ b t k s) (hk : b * t + k < (lenV s₀).toNat)
    {r : Reg8} (hv : (s.gpr r.reg).setWidth 8 = (L s₀)[b * t + k]!) {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', G s₀ b t (k + 1) s' → (∀ x, s'.gpr x = s.gpr x) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ .edi k) r :: is)) s Q := by
  have fo := hp.o_fit
  have e : s.ea (at_ .edi k) = oA s₀ + BitVec.ofNat 64 (b * t + k) := by
    show (s.gpr .edi + BitVec.ofNat 32 k).setWidth 64 = _
    rw [h.edi, ea_add (by omega)]
  have hin : InRegions s.wr (s.ea (at_ .edi k)) 1 :=
    ⟨oR s₀, by rw [h.wr, P0_wr, hp.wr]; simp, by rw [e]; exact contains_at (by omega) fo⟩
  refine wp_st8 hin (kk _ ⟨h.esp, h.rd, h.wr, h.esi, h.edi, h.ecx, ?_, ?_⟩ fun _ => rfl)
  · rw [e]; exact h.frame.writeW (List.mem_singleton_self _) _ (contains_at (by omega) fo)
  · rw [e]
    exact bytes_extend1 (by omega) h.out hv

/-- Bytes `k … k + 3` of group `t`, the bytes of `ebx = W`. -/
theorem st4_spec {s₀ s : State} (hp : Pre s₀) {b t k : Nat} (h : G s₀ b t k s)
    (hk : b * t + k + 4 ≤ (lenV s₀).toNat) {W : Nat} (hW : (s.gpr .ebx).toNat = W)
    (hb : ∀ i < 4, BitVec.ofNat 8 (W / 2 ^ (8 * i)) = (L s₀)[b * t + k + i]!) {is : List Instr}
    {Q : State → Prop} (kk : ∀ s', G s₀ b t (k + 4) s' → Regs [.eax] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (st4 k ++ is)) s Q := by
  simp only [st4, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ o₁ e₁ => ?_
  have t0 : (s₁.gpr .eax).toNat = W / 2 ^ (8 * 0) := by rw [e₁, hW, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  refine (h.of_only o₁ (by decide)).st8 hp (k := k) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t0]; exact hb 0 (by decide)) fun s₂ h₂ g₂ => ?_
  refine wp_shr (by decide) (by decide) fun s₃ o₃ e₃ => ?_
  have t1 : (s₃.gpr .eax).toNat = W / 2 ^ (8 * 1) := by
    rw [e₃, toNat_shr, g₂, t0, Nat.div_div_eq_div_mul]
  refine (h₂.of_only o₃ (by decide)).st8 hp (k := k + 1) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t1]; exact hb 1 (by decide)) fun s₄ h₄ g₄ => ?_
  refine wp_shr (by decide) (by decide) fun s₅ o₅ e₅ => ?_
  have t2 : (s₅.gpr .eax).toNat = W / 2 ^ (8 * 2) := by
    rw [e₅, toNat_shr, g₄, t1, Nat.div_div_eq_div_mul]
  refine (h₄.of_only o₅ (by decide)).st8 hp (k := k + 1 + 1) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t2]; exact hb 2 (by decide)) fun s₆ h₆ g₆ => ?_
  refine wp_shr (by decide) (by decide) fun s₇ o₇ e₇ => ?_
  have t3 : (s₇.gpr .eax).toNat = W / 2 ^ (8 * 3) := by
    rw [e₇, toNat_shr, g₆, t2, Nat.div_div_eq_div_mul]
  refine (h₆.of_only o₇ (by decide)).st8 hp (k := k + 1 + 1 + 1) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t3]; exact hb 3 (by decide)) fun s₈ h₈ g₈ => ?_
  refine kk s₈ h₈ ⟨fun x hx => ?_, ?_, ?_⟩
  · rw [g₈, o₇.gpr x (by simpa using hx), g₆, o₅.gpr x (by simpa using hx), g₄, o₃.gpr x (by simpa using hx),
      g₂, o₁.gpr x (by simpa using hx)]
  · rw [h₈.rd, h.rd]
  · rw [h₈.wr, h.wr]

/-- Bytes `k … k + 2` of group `t`, the low bytes of `ebx = W`. -/
theorem st3_spec {s₀ s : State} (hp : Pre s₀) {b t k : Nat} (h : G s₀ b t k s)
    (hk : b * t + k + 3 ≤ (lenV s₀).toNat) {W : Nat} (hW : (s.gpr .ebx).toNat = W)
    (hb : ∀ i < 3, BitVec.ofNat 8 (W / 2 ^ (8 * i)) = (L s₀)[b * t + k + i]!) {is : List Instr}
    {Q : State → Prop} (kk : ∀ s', G s₀ b t (k + 3) s' → Regs [.eax] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (st3 k ++ is)) s Q := by
  simp only [st3, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ o₁ e₁ => ?_
  have t0 : (s₁.gpr .eax).toNat = W / 2 ^ (8 * 0) := by rw [e₁, hW, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  refine (h.of_only o₁ (by decide)).st8 hp (k := k) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t0]; exact hb 0 (by decide)) fun s₂ h₂ g₂ => ?_
  refine wp_shr (by decide) (by decide) fun s₃ o₃ e₃ => ?_
  have t1 : (s₃.gpr .eax).toNat = W / 2 ^ (8 * 1) := by
    rw [e₃, toNat_shr, g₂, t0, Nat.div_div_eq_div_mul]
  refine (h₂.of_only o₃ (by decide)).st8 hp (k := k + 1) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t1]; exact hb 1 (by decide)) fun s₄ h₄ g₄ => ?_
  refine wp_shr (by decide) (by decide) fun s₅ o₅ e₅ => ?_
  have t2 : (s₅.gpr .eax).toNat = W / 2 ^ (8 * 2) := by
    rw [e₅, toNat_shr, g₄, t1, Nat.div_div_eq_div_mul]
  refine (h₄.of_only o₅ (by decide)).st8 hp (k := k + 1 + 1) (r := .al) (by omega)
    (by rw [show (Reg8.al).reg = .eax from rfl, setWidth8_eq, t2]; exact hb 2 (by decide)) fun s₆ h₆ g₆ => ?_
  refine kk s₆ h₆ ⟨fun x hx => ?_, ?_, ?_⟩
  · rw [g₆, o₅.gpr x (by simpa using hx), g₄, o₃.gpr x (by simpa using hx), g₂, o₁.gpr x (by simpa using hx)]
  · rw [h₆.rd, h.rd]
  · rw [h₆.wr, h.wr]

/-- The end of a group: on to the next. -/
theorem next_spec {s₀ s : State} {b t : Nat} (ht : t < 32) (h : G s₀ b t b s) :
    WP isa (.block (nextG 32 b)) s fun s' => G s₀ b (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nextG, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, ?_, ?_, ?_, h.frame, fun j hj => h.out j (by rw [Nat.mul_succ] at hj; omega)⟩,
    ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true, h.esi]
    rw [add_ofNat_add, Nat.mul_succ]
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.edi]
    rw [add_ofNat_add, Nat.mul_succ]
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## `d` = 5: five bytes of eight coefficients -/

section
variable {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : dN s₀ = d) {t : Nat} (ht : t < 32)
include hp hd ht

/-- Compressed coefficient `8 t + i`, from memory. -/
theorem cv {i : Nat} (hi : i < 8) :
    compress d (F s₀)[8 * t + i]! = cf d (coeffAt s₀.mem (fA s₀) (8 * t + i)).toNat := by
  have := hp.C_eq (i := 8 * t + i) (by omega)
  rw [C, hd] at this
  exact this

end

theorem step5 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 5) {t : Nat} (ht : t < 32) {s : State}
    (h : G s₀ 5 t 0 s) :
    WP isa (.block pack5Body) s fun s' => G s₀ 5 (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  have hdm : (5 : Nat) ∈ Spec.MlKem1024.compressWidths := hd ▸ hp.d_mem
  have hl := hp.len_eq
  rw [hd] at hl
  generalize ha : (fun i => (coeffAt s₀.mem (fA s₀) (8 * t + i)).toNat) = a
  have hav : ∀ i, (coeffAt s₀.mem (fA s₀) (8 * t + i)).toNat = a i := fun i => by rw [← ha]
  have c : ∀ i < 8, compress 5 (F s₀)[8 * t + i]! = cf 5 (a i) := fun i hi => by
    rw [cv hp hd ht hi, hav]
  have lc : ∀ i, cf 5 (a i) < 32 := fun i => cf_lt 5 _
  have co : ∀ {s'}, G s₀ 5 t 0 s' → ∀ i < 8, Coef s' i (a i) := fun h' i hi => by
    rw [← hav]; exact h'.coef hp ht hi
  unfold pack5Body
  refine ldC_spec hdm 7 _ s _ (co h 7 (by decide)) fun s₁ o₁ v₁ => ?_
  refine wp_mov fun s₂ o₂ e₂ => wp_ror (by decide) (by decide) fun s₃ o₃ e₃ => ?_
  have bp₃ : (s₃.gpr .ebp).toNat = cf 5 (a 7) * 2 ^ 3 := by
    have := ror_shl (d := 3) (A := cf 5 (a 7)) (by decide) (by decide) (s₂.gpr .ebp) (by rw [e₂, v₁])
      (by have := lc 7; omega)
    rw [e₃]; exact this
  have h₃ := h.of_only ((o₁.trans o₂).trans o₃) (by decide)
  refine ldC_spec hdm 6 _ s₃ _ (co h₃ 6 (by decide)) fun s₄ o₄ v₄ => ?_
  refine wp_mov fun s₅ o₅ e₅ => wp_and fun s₆ o₆ e₆ => wp_shr (by decide) (by decide) fun s₇ o₇ e₇ => ?_
  refine wp_addr fun s₈ o₈ e₈ => ?_
  have h₈ := h₃.of_only ((((o₄.trans o₅).trans o₆).trans o₇).trans o₈) (by decide)
  have bx₈ : (s₈.gpr .ebx).toNat = cf 5 (a 6) % 4 := by
    rw [o₈.gpr _ (by decide), o₇.gpr _ (by decide), e₆, e₅, show (3 : BitVec 32) = BitVec.ofNat 32 (2 ^ 2 - 1) from rfl,
      toNat_and_mask _ _ (by decide), v₄]
  have bp₈ : (s₈.gpr .ebp).toNat = cf 5 (a 7) * 8 + cf 5 (a 6) / 4 := by
    have h7 := lc 7
    have ax₆ : s₆.gpr .eax = s₄.gpr .eax := by rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide)]
    have bp₇ : s₇.gpr .ebp = s₃.gpr .ebp := by
      rw [o₇.gpr _ (by decide), o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide)]
    rw [e₈, bp₇, e₇, ax₆, BitVec.toNat_add, toNat_shr, bp₃, v₄]
    omega
  refine accSs_spec hdm 0 a 6 _ s₈ _ _ (fun i hi => by rw [Nat.zero_add]; exact co h₈ i (by omega)) bx₈
    (by have := Nat.mod_lt (cf 5 (a 6)) (show 4 > 0 by decide); omega) fun s₉ o₉ v₉ => ?_
  have h₉ := h₈.of_only o₉ (by decide)
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.reduceMul, Nat.reducePow] at v₉
  refine st4_spec hp h₉ (k := 0) (by omega) v₉ (fun i hi => ?_) fun s₁₀ h₁₀ g₁₀ => ?_
  · have l := lc
    have c0 : compress 5 (F s₀)[8 * t]! = cf 5 (a 0) := c 0 (by decide)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.reducePow]
    · rw [L, hd, compressEncode5_0 _ ht, c0, c 1 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2, l 3, l 4, l 5])
    · rw [L, hd, compressEncode5_1 _ ht, c 1 (by decide), c 2 (by decide), c 3 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2, l 3, l 4, l 5])
    · rw [L, hd, compressEncode5_2 _ ht, c 3 (by decide), c 4 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2, l 3, l 4, l 5])
    · rw [L, hd, compressEncode5_3 _ ht, c 4 (by decide), c 5 (by decide), c 6 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2, l 3, l 4, l 5])
  refine wp_mov fun s₁₁ o₁₁ e₁₁ => ?_
  refine (h₁₀.of_only o₁₁ (by decide)).st8 hp (k := 0 + 4) (r := .al) (by omega) ?_ fun s₁₂ h₁₂ _ => ?_
  · rw [show (Reg8.al).reg = .eax from rfl, e₁₁, g₁₀.gpr _ (by decide), o₉.gpr _ (by decide), setWidth8_eq, bp₈,
      show 5 * t + (0 + 4) = 5 * t + 4 from rfl, L, hd, compressEncode5_4 _ ht, c 6 (by decide), c 7 (by decide)]
    exact ofNat8_eq (by omega)
  exact next_spec ht h₁₂

/-! ## `d` = 11: eleven bytes of eight coefficients -/

theorem step11 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 11) {t : Nat} (ht : t < 32) {s : State}
    (h : G s₀ 11 t 0 s) :
    WP isa (.block pack11Body) s fun s' => G s₀ 11 (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  have hdm : (11 : Nat) ∈ Spec.MlKem1024.compressWidths := hd ▸ hp.d_mem
  have hl := hp.len_eq
  rw [hd] at hl
  generalize ha : (fun i => (coeffAt s₀.mem (fA s₀) (8 * t + i)).toNat) = a
  have hav : ∀ i, (coeffAt s₀.mem (fA s₀) (8 * t + i)).toNat = a i := fun i => by rw [← ha]
  have c : ∀ i < 8, compress 11 (F s₀)[8 * t + i]! = cf 11 (a i) := fun i hi => by
    rw [cv hp hd ht hi, hav]
  have c0 : compress 11 (F s₀)[8 * t]! = cf 11 (a 0) := c 0 (by decide)
  have lc : ∀ i, cf 11 (a i) < 2048 := fun i => cf_lt 11 _
  have co : ∀ {s' k}, G s₀ 11 t k s' → ∀ i < 8, Coef s' i (a i) := fun h' i hi => by
    rw [← hav]; exact h'.coef hp ht hi
  unfold pack11Body
  -- Bytes 0–3.
  refine ldC_spec hdm 2 _ s _ (co h 2 (by decide)) fun s₁ o₁ v₁ => ?_
  refine wp_mov fun s₂ o₂ e₂ => wp_shr (by decide) (by decide) fun s₃ o₃ e₃ => ?_
  refine wp_mov fun s₄ o₄ e₄ => wp_and fun s₅ o₅ e₅ => ?_
  have h₅ := h.of_only ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅) (by decide)
  have bp₅ : (s₅.gpr .ebp).toNat = cf 11 (a 2) / 1024 := by
    rw [o₅.gpr _ (by decide), o₄.gpr _ (by decide), e₃, e₂, toNat_shr, v₁]
  have bx₅ : (s₅.gpr .ebx).toNat = cf 11 (a 2) % 1024 := by
    rw [e₅, e₄, o₃.gpr _ (by decide), o₂.gpr _ (by decide),
      show (1023 : BitVec 32) = BitVec.ofNat 32 (2 ^ 10 - 1) from rfl, toNat_and_mask _ _ (by decide), v₁]
  refine accSs_spec hdm 0 a 2 _ s₅ _ _ (fun i hi => by rw [Nat.zero_add]; exact co h₅ i (by omega)) bx₅
    (by have := Nat.mod_lt (cf 11 (a 2)) (show 1024 > 0 by decide); omega) fun s₆ o₆ v₆ => ?_
  have h₆ := h₅.of_only o₆ (by decide)
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.reduceMul, Nat.reducePow] at v₆
  refine st4_spec hp h₆ (k := 0) (by omega) v₆ (fun i hi => ?_) fun s₇ h₇ g₇ => ?_
  · have l := lc
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.reducePow]
    · rw [L, hd, compressEncode11_0 _ ht, c0]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2])
    · rw [L, hd, compressEncode11_1 _ ht, c0, c 1 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2])
    · rw [L, hd, compressEncode11_2 _ ht, c 1 (by decide), c 2 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2])
    · rw [L, hd, compressEncode11_3 _ ht, c 2 (by decide)]
      exact ofNat8_eq (by omega_using [l 0, l 1, l 2])
  have bp₇ : (s₇.gpr .ebp).toNat = cf 11 (a 2) / 1024 := by
    rw [g₇.gpr _ (by decide), o₆.gpr _ (by decide), bp₅]
  -- Bytes 4–7.
  refine ldC_spec hdm 5 _ s₇ _ (co h₇ 5 (by decide)) fun s₈ o₈ v₈ => ?_
  refine wp_mov fun s₉ o₉ e₉ => wp_and fun s₁₀ o₁₀ e₁₀ => ?_
  have h₁₀ := h₇.of_only ((o₈.trans o₉).trans o₁₀) (by decide)
  have bx₁₀ : (s₁₀.gpr .ebx).toNat = cf 11 (a 5) % 512 := by
    rw [e₁₀, e₉, show (511 : BitVec 32) = BitVec.ofNat 32 (2 ^ 9 - 1) from rfl, toNat_and_mask _ _ (by decide), v₈]
  refine accSs_spec hdm 3 (fun i => a (3 + i)) 2 _ s₁₀ _ _ (fun i hi => co h₁₀ (3 + i) (by omega)) bx₁₀
    (by have := Nat.mod_lt (cf 11 (a 5)) (show 512 > 0 by decide); omega) fun s₁₁ o₁₁ v₁₁ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow, Nat.reduceAdd] at v₁₁
  refine wp_ror (by decide) (by decide) fun s₁₂ o₁₂ e₁₂ => wp_addr fun s₁₃ o₁₃ e₁₃ => ?_
  have h₁₃ := (h₁₀.of_only o₁₁ (by decide)).of_only (o₁₂.trans o₁₃) (by decide)
  have bx₁₃ : (s₁₃.gpr .ebx).toNat = (cf 11 (a 5) % 512 * 4194304 + (cf 11 (a 3) + cf 11 (a 4) * 2048)) * 2 +
      cf 11 (a 2) / 1024 := by
    have l3 := lc 3; have l4 := lc 4
    have hm := Nat.mod_lt (cf 11 (a 5)) (show 512 > 0 by decide)
    have r := ror_shl (d := 1) (by decide) (by decide) (s₁₁.gpr .ebx) v₁₁ (by omega)
    rw [e₁₃, BitVec.toNat_add, e₁₂, r, o₁₂.gpr .ebp (by decide), o₁₁.gpr .ebp (by decide),
      o₁₀.gpr .ebp (by decide), o₉.gpr .ebp (by decide), o₈.gpr .ebp (by decide), bp₇]
    have := lc 2
    omega
  refine st4_spec hp h₁₃ (k := 4) (by omega) bx₁₃ (fun i hi => ?_) fun s₁₄ h₁₄ g₁₄ => ?_
  · have l := lc
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.reducePow,
        Nat.add_assoc, Nat.reduceAdd]
    · rw [L, hd, compressEncode11_4 _ ht, c 2 (by decide), c 3 (by decide)]
      exact ofNat8_eq (by omega_using [l 2, l 3, l 4, l 5])
    · rw [L, hd, compressEncode11_5 _ ht, c 3 (by decide), c 4 (by decide)]
      exact ofNat8_eq (by omega_using [l 2, l 3, l 4, l 5])
    · rw [L, hd, compressEncode11_6 _ ht, c 4 (by decide), c 5 (by decide)]
      exact ofNat8_eq (by omega_using [l 2, l 3, l 4, l 5])
    · rw [L, hd, compressEncode11_7 _ ht, c 5 (by decide)]
      exact ofNat8_eq (by omega_using [l 2, l 3, l 4, l 5])
  -- Bytes 8–10.
  refine ldC_spec hdm 5 _ s₁₄ _ (co h₁₄ 5 (by decide)) fun s₁₅ o₁₅ v₁₅ => ?_
  refine wp_shr (by decide) (by decide) fun s₁₆ o₁₆ e₁₆ => wp_mov fun s₁₇ o₁₇ e₁₇ => ?_
  have h₁₇ := h₁₄.of_only ((o₁₅.trans o₁₆).trans o₁₇) (by decide)
  have bp₁₇ : (s₁₇.gpr .ebp).toNat = cf 11 (a 5) / 512 := by
    rw [e₁₇, e₁₆, toNat_shr, v₁₅]
  refine ldC_spec hdm 7 _ s₁₇ _ (co h₁₇ 7 (by decide)) fun s₁₈ o₁₈ v₁₈ => ?_
  refine wp_mov fun s₁₉ o₁₉ e₁₉ => ?_
  have h₁₉ := h₁₇.of_only (o₁₈.trans o₁₉) (by decide)
  refine accSs_spec hdm 6 (fun i => a (6 + i)) 1 _ s₁₉ _ _ (fun i hi => co h₁₉ (6 + i) (by omega))
    (by rw [e₁₉, v₁₈]) (by have := lc 7; omega) fun s₂₀ o₂₀ v₂₀ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reducePow] at v₂₀
  refine wp_ror (by decide) (by decide) fun s₂₁ o₂₁ e₂₁ => wp_addr fun s₂₂ o₂₂ e₂₂ => ?_
  have h₂₂ := (h₁₉.of_only o₂₀ (by decide)).of_only (o₂₁.trans o₂₂) (by decide)
  have bx₂₂ : (s₂₂.gpr .ebx).toNat = (cf 11 (a 7) * 2048 + cf 11 (a 6)) * 4 + cf 11 (a 5) / 512 := by
    have l6 := lc 6; have l7 := lc 7
    have r := ror_shl (d := 2) (by decide) (by decide) (s₂₀.gpr .ebx) v₂₀ (by omega)
    rw [e₂₂, BitVec.toNat_add, e₂₁, r, o₂₁.gpr .ebp (by decide), o₂₀.gpr .ebp (by decide),
      o₁₉.gpr .ebp (by decide), o₁₈.gpr .ebp (by decide), bp₁₇]
    have := lc 5
    omega
  refine st3_spec hp h₂₂ (k := 8) (by omega) bx₂₂ (fun i hi => ?_) fun s₂₃ h₂₃ _ => next_spec ht h₂₃
  have l := lc
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
    simp only [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul, Nat.reducePow,
      Nat.add_assoc, Nat.reduceAdd]
  · rw [L, hd, compressEncode11_8 _ ht, c 5 (by decide), c 6 (by decide)]
    exact ofNat8_eq (by omega_using [l 5, l 6, l 7])
  · rw [L, hd, compressEncode11_9 _ ht, c 6 (by decide), c 7 (by decide)]
    exact ofNat8_eq (by omega_using [l 5, l 6, l 7])
  · rw [L, hd, compressEncode11_10 _ ht, c 7 (by decide)]
    exact ofNat8_eq (by omega_using [l 5, l 6, l 7])

/-! ## The function -/

/-- After `ceInit5`. -/
structure Init (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = fP s₀
  edi : s.gpr .edi = oP s₀
  ev : eval .e s = some (decide (dN s₀ = 5))

theorem pub_esp {s₀ s₀' : State} (hq : Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

theorem init_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Init (.block ceInit5) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₁ := P0_argAddr s₀ 1
    have a₂ := P0_argAddr s₀ 2
    have i₀ := P0_argIn (s₀ := s₀) (n := 4) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₁ := P0_argIn (s₀ := s₀) (n := 4) (i := 1) (by omega) fit (by simp [hp.wr])
    have i₂ := P0_argIn (s₀ := s₀) (n := 4) (i := 2) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 4) (i := 0) (by omega) fit hp.stk_a
    have v₁ := P0_arg hp.sp (n := 4) (i := 1) (by omega) fit hp.stk_a
    have v₂ := P0_arg hp.sp (n := 4) (i := 2) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp (config := {decide := true}) only [ceInit5, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂, ite_true, ite_false,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, rfl, by simp, by simp, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', pub_esp hq]

theorem ecx_piece (d b : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => Init s₀ s ∧ dN s₀ = d)
      (fun s₀ s => G s₀ b 0 0 s ∧ dN s₀ = d) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hd⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    ht
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp [h.edi], by simp,
    (by rw [h.mem]; exact Frame.refl _ _), fun j hj => absurd hj (by omega)⟩, hd⟩

theorem loop_piece {d b : Nat} (body : List Instr)
    (hstep : ∀ t < 32, ∀ s₀ s, Pre s₀ → dN s₀ = d → G s₀ b t 0 s →
      WP isa (.block body) s fun s' => G s₀ b (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => G s₀ b 0 0 s ∧ dN s₀ = d) (fun s₀ s => G s₀ b 32 0 s ∧ dN s₀ = d)
      (.loop (.block body) .ne) :=
  Piece.countLoop (by decide) (fun t s₀ s => G s₀ b t 0 s ∧ dN s₀ = d) [.esp, .esi, .edi, .ecx]
    (fun t ht s₀ s hp ⟨h, hd⟩ => (hstep t ht s₀ s hp hd h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hd⟩, e⟩)
    (fun t _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.esi, h'.esi, fP, fP, hq.2.1]
      · rw [h.edi, h'.edi, oP, oP, hq.2.2.2.1]
      · rw [h.ecx, h'.ecx]) ht

theorem branch_piece {d : Nat} (body : List Instr)
    (hstep : ∀ t < 32, ∀ s₀ s, Pre s₀ → dN s₀ = d → G s₀ d t 0 s →
      WP isa (.block body) s fun s' => G s₀ d (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true)
    {hc' : Taint.Hint VG.X86.Taint.T}
    (ht' : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) hc').isSome = true) :
    Piece Pre Pub (fun s₀ s => Init s₀ s ∧ dN s₀ = d) Fin (countedLoop 32 body) :=
  (Piece.seq (ecx_piece d d ht') (loop_piece body hstep ht)).mono (fun _ _ _ h => h)
    fun _ _ _ ⟨h, hd⟩ => h.fin hd

theorem ite_pub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
    decide (dN s₀ = 5) = decide (dN s₀' = 5) := fun _ _ _ _ hq => by rw [dN, dN, dV, dV, hq.2.2.1]

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block ceInit5) (.ite .e (countedLoop 32 pack5Body) (countedLoop 32 pack11Body))) := by
  refine Piece.seq init_piece (Piece.ite _ (fun _ _ _ h => h.ev) ite_pub ?_ ?_)
  · exact (branch_piece (d := 5) pack5Body (fun t ht s₀ s hp hd h => step5 hp hd ht h) (by taint_decide)
      (by taint_decide)).mono (fun _ _ _ ⟨h, e⟩ => ⟨h, of_decide_eq_true e⟩) fun _ _ _ h => h
  · exact (branch_piece (d := 11) pack11Body (fun t ht s₀ s hp hd h => step11 hp hd ht h) (by taint_decide)
      (by taint_decide)).mono
      (fun s₀ _ hp ⟨h, e⟩ => ⟨h, by
        have h5 := of_decide_eq_false e
        rcases mem_compressWidths1024 hp.d_mem with h' | h' <;> [exact absurd h' h5; exact h']⟩)
      fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem1024.X86.compressEncode :=
  Piece.leaf (fun s₀ => [oR s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_o, hp.ret_o⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `5`, `0x400` and `160` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 5 else if a = 0x500d then 4 else if a = 0x5010 then 160 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.compressEncode
    (Spec.MlKem1024.compressEncodeContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    have hp := Pre.of h₀
    rw [hm, hp.len_eq]
    exact bytesAt_eq! (compressEncode_length _ _) fun j hj => hinv.out j hj
  · let st := satState satMem [⟨0, 1024⟩] [⟨0x400, 160⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 5 := by decide
    have a2 : arg st 2 = 0x400 := by decide
    have a3 : arg st 3 = 160 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide,
      by decide, by decide, reduced_below (fun a ha => ?_) 0 (by decide)⟩
    all_goals first
      | exact Region.disjoint_of_sep (by decide)
      | (show satMem a = 0
         simp only [satMem]
         rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega),
           ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])

end VG.Proof.MlKem1024.X86.CompressEncode
