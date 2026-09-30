import VerifiedGarbage.Proof.MlKem1024.X86.Unpack
import VerifiedGarbage.Proof.MlKem.Encode1024
import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_decode_decompress`

Untrusted: everything here is checked by Lean. The branch on `d` depends
only on `d`; each branch is a loop over the 32 groups of `d` bytes, loaded
into `ebx` by `ldW` (`Unpack.lean`), whose fields (`fieldAt`, `crossAt`) are
decompressed in order into the coefficients of `decodeDecompress5_*` and
`decodeDecompress11_*` (`Encode1024.lean`). `D b t k` is the state within
group `t` of `b` bytes, after its first `k` coefficients.
-/

namespace VG.Proof.MlKem1024.X86.DecodeDecompress

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem1024.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
abbrev bP : BitVec 32 := arg s₀ 0
abbrev lenV : BitVec 32 := arg s₀ 1
abbrev dV : BitVec 32 := arg s₀ 2
abbrev fP : BitVec 32 := arg s₀ 3
abbrev bA : Addr := (bP s₀).setWidth 64
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev bR : Region := ⟨bA s₀, (lenV s₀).toNat⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
abbrev dN : Nat := (dV s₀).toNat
/-- The input bytes. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (lenV s₀).toNat
/-- The value of coefficient `i`. -/
abbrev V (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decodeDecompress (dN s₀) (B s₀))[i]!).val
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 16 ≤ 2 ^ 32
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
  b_fit : (bP s₀).toNat + (lenV s₀).toNat ≤ 2 ^ 32
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  d_mem : dN s₀ ∈ Spec.MlKem1024.compressWidths
  len_eq : (lenV s₀).toNat = 32 * dN s₀

theorem Pre.of {s₀ : State} (h : (Spec.MlKem1024.decodeDecompressContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stk_eq : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem b_keep {s : State} (hf : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem) {j : Nat}
    (hj : j < (lenV s₀).toNat) : s.mem (bA s₀ + BitVec.ofNat 64 j) = (B s₀).getD j 0 := by
  have hf₁ := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rw [saveRegs_len] at hf₁
  have l : (bR s₀).len ≤ 2 ^ 64 := by show (lenV s₀).toNat ≤ 2 ^ 64; have := (lenV s₀).isLt; omega
  rw [bytesAt_getD _ _ hj, hf.bytes (R := bR s₀) (by simpa using hp.b_f) l hj,
    hf₁.bytes (R := bR s₀) (by simpa [← hp.stk_eq] using hp.stk_b.symm) l hj]

theorem B_len : (B s₀).length = 32 * dN s₀ := by rw [B, bytesAt_length, hp.len_eq]

end Pre

/-- Within group `t` of `b` bytes, after its first `k` coefficients, counting down from 32. -/
structure D (s₀ : State) (b t k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = bP s₀ + BitVec.ofNat 32 (b * t)
  edi : s.gpr .edi = fP s₀ + BitVec.ofNat 32 (32 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (32 - t)
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 8 * t + k, coeffAt s.mem (fA s₀) i = V s₀ i

theorem D.of_only {s₀ s s' : State} {b t k : Nat} (h : D s₀ b t k s) {ds : List Reg} (o : Only ds s s')
    (hd : Reg.esp ∉ ds ∧ Reg.esi ∉ ds ∧ Reg.edi ∉ ds ∧ Reg.ecx ∉ ds) : D s₀ b t k s' :=
  ⟨by rw [o.gpr _ hd.1, h.esp], by rw [o.rd, h.rd], by rw [o.wr, h.wr], by rw [o.gpr _ hd.2.1, h.esi],
    by rw [o.gpr _ hd.2.2.1, h.edi], by rw [o.gpr _ hd.2.2.2, h.ecx], o.mem ▸ h.frame,
    fun j hj => o.mem ▸ h.coef j hj⟩

/-- The end of every branch. -/
structure Fin (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  coef : ∀ i < 256, coeffAt s.mem (fA s₀) i = V s₀ i

theorem D.fin {s₀ s : State} {b : Nat} (h : D s₀ b 32 0 s) : Fin s₀ s :=
  ⟨h.esp, h.rd, h.wr, h.frame, fun i hi => h.coef i (by omega)⟩

/-- Byte `o` of group `t`, from `esi`. -/
theorem D.byte {s₀ s : State} (hp : Pre s₀) {b t k : Nat} (h : D s₀ b t k s) {o : Nat}
    (ho : b * t + o < (lenV s₀).toNat) : Byt s o ((B s₀).getD (b * t + o) 0).toNat := by
  have fb := hp.b_fit
  have e : s.ea (at_ .esi o) = bA s₀ + BitVec.ofNat 64 (b * t + o) := by
    show (s.gpr .esi + BitVec.ofNat 32 o).setWidth 64 = _
    rw [h.esi, ea_add (by omega)]
  refine ⟨?_, ?_⟩
  · rw [e]; exact ⟨bR s₀, by rw [h.rd, h.wr, pushed_rd, P0_wr, hp.rd]; simp, contains_at (by omega) fb⟩
  · rw [e, hp.b_keep h.frame ho]

/-- Coefficient `8 t + k` from `eax = y`. -/
theorem D.st {s₀ s : State} (hp : Pre s₀) {d b t k : Nat} (hd : dN s₀ = d) (h : D s₀ b t k s) (ht : t < 32)
    (hk : k < 8) {y : Nat} (hy : y < 2 ^ d) (hax : (s.gpr .eax).toNat = y)
    (hv : (decodeDecompress d (B s₀))[8 * t + k]! = decompress d y) {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', D s₀ b t (k + 1) s' → s'.gpr .ebx = s.gpr .ebx → WP isa (.block is) s' Q) :
    WP isa (.block (decSt d k ++ is)) s Q := by
  have hdm : d ∈ Spec.MlKem1024.compressWidths := hd ▸ hp.d_mem
  have ff := hp.f_fit
  have e : s.ea (at_ .edi (4 * k)) = coeffAddr (fA s₀) (8 * t + k) := by
    show (s.gpr .edi + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [h.edi, ea_add (by omega)]
    congr 2; omega
  have hn : 8 * t + k < n := by rw [n_eq]; omega
  refine decSt_spec hdm k is s Q hy hax
    ⟨polyRegion (fA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, by rw [e]; exact coeff_contains _ hn⟩
    fun s' r m => kk s' ⟨by rw [r.gpr _ (by decide), h.esp], by rw [r.rd, h.rd], by rw [r.wr, h.wr],
      by rw [r.gpr _ (by decide), h.esi], by rw [r.gpr _ (by decide), h.edi], by rw [r.gpr _ (by decide), h.ecx],
      ?_, ?_⟩ (r.gpr _ (by decide))
  · rw [m, e]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn)
  · intro i hi
    rw [m, e, coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) hn]
    by_cases ei : 8 * t + k = i
    · rw [ite_eq_left ei, ← ei, V, hd, hv, dv_eq' hdm hy]
    · rw [ite_eq_right ei]; exact h.coef i (by omega)

/-- Coefficient `8 t + k`, the field of `ebx = W` at bit `sh`. -/
theorem D.field {s₀ s : State} (hp : Pre s₀) {d b t k : Nat} (hd : dN s₀ = d) (h : D s₀ b t k s) (ht : t < 32)
    (hk : k < 8) {W : Nat} (hW : (s.gpr .ebx).toNat = W) {sh : Nat} (hsh : sh ≤ 31)
    (hv : (decodeDecompress d (B s₀))[8 * t + k]! = decompress d (W / 2 ^ sh % 2 ^ d)) {is : List Instr}
    {Q : State → Prop} (kk : ∀ s', D s₀ b t (k + 1) s' → s'.gpr .ebx = s.gpr .ebx → WP isa (.block is) s' Q) :
    WP isa (.block (fieldAt d sh k ++ is)) s Q := by
  have hdm : d ∈ Spec.MlKem1024.compressWidths := hd ▸ hp.d_mem
  have hd' : d < 32 := by rcases mem_compressWidths1024 hdm with rfl | rfl <;> decide
  rw [fieldAt, List.append_assoc, List.cons_append]
  refine shrFrom_spec sh hsh _ s Q fun s₁ o₁ v₁ => wp_and fun s₂ o₂ v₂ => ?_
  have o := o₁.trans o₂
  refine (h.of_only o (by decide)).st hp hd ht hk (Nat.mod_lt _ (Nat.two_pow_pos d)) ?_ hv fun s' h' e' => ?_
  · rw [v₂, v₁, toNat_and_mask _ _ hd', toNat_shr, hW]
  · exact kk s' h' (by rw [e', o.gpr _ (by decide)])

/-- Coefficient `8 t + k`, the field of `ebx = W` at bit `sh` continued by the low `e` bits of
byte `o`, at bit `m` of the field. -/
theorem D.cross {s₀ s : State} (hp : Pre s₀) {d b t k : Nat} (hd : dN s₀ = d) (h : D s₀ b t k s) (ht : t < 32)
    (hk : k < 8) {W : Nat} (hW : (s.gpr .ebx).toNat = W) {sh o e m : Nat} (hsh : 1 ≤ sh ∧ sh ≤ 31)
    (hm : 1 ≤ m ∧ m ≤ 31) (hem : e + m ≤ 32) (he : e < 32) {x : Nat} (hx : Byt s o x)
    (hy : W / 2 ^ sh + x % 2 ^ e * 2 ^ m < 2 ^ d)
    (hv : (decodeDecompress d (B s₀))[8 * t + k]! = decompress d (W / 2 ^ sh + x % 2 ^ e * 2 ^ m))
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', D s₀ b t (k + 1) s' → s'.gpr .ebx = s.gpr .ebx → WP isa (.block is) s' Q) :
    WP isa (.block (crossAt d sh o e m k ++ is)) s Q := by
  have hW' : W < 2 ^ 32 := by rw [← hW]; exact (s.gpr .ebx).isLt
  rw [crossAt, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_ldb hx fun s₁ o₁ v₁ => wp_and fun s₂ o₂ v₂ => wp_ror (by omega) (by omega) fun s₃ o₃ v₃ => ?_
  refine wp_mov fun s₄ o₄ v₄ => wp_shr hsh.1 hsh.2 fun s₅ o₅ v₅ => wp_addr fun s₆ o₆ v₆ => ?_
  have o := (((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆)
  have hxe : (s₂.gpr .edx).toNat = x % 2 ^ e := by rw [v₂, toNat_and_mask _ _ he, v₁]
  have hxl : x % 2 ^ e < 2 ^ (32 - m) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos e)) (Nat.pow_le_pow_right (by decide) (by omega))
  have r := ror_shl (d := m) hm.1 (by omega) (s₂.gpr .edx) hxe hxl
  have h32 : 2 ^ d ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by
    have := hp.d_mem; rw [hd] at this; rcases mem_compressWidths1024 this with rfl | rfl <;> decide)
  have hsum : W / 2 ^ sh + x % 2 ^ e * 2 ^ m < 2 ^ 32 := Nat.lt_of_lt_of_le hy h32
  refine (h.of_only o (by decide)).st hp hd ht hk hy ?_ hv fun s' h' e' => ?_
  · rw [v₆, BitVec.toNat_add, v₅, v₄, o₃.gpr .ebx (by decide), o₂.gpr .ebx (by decide), o₁.gpr .ebx (by decide),
      toNat_shr, hW, o₅.gpr .edx (by decide), o₄.gpr .edx (by decide), v₃, r, Nat.mod_eq_of_lt hsum]
  · exact kk s' h' (by rw [e', o.gpr _ (by decide)])

/-- The end of a group: on to the next. -/
theorem next_spec {s₀ s : State} {b t : Nat} (ht : t < 32) (h : D s₀ b t 8 s) :
    WP isa (.block (nextG b 32)) s fun s' => D s₀ b (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [nextG, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, ?_, ?_, ?_, h.frame, fun j hj => h.coef j (by rw [Nat.mul_succ] at hj; omega)⟩,
    ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide, ite_false, ite_true, h.esi]
    rw [add_ofNat_add, Nat.mul_succ]
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.edi]
    rw [add_ofNat_add, Nat.mul_succ]
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)

/-! ## `d` = 5: eight coefficients of five bytes -/

theorem step5 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 5) {t : Nat} (ht : t < 32) {s : State}
    (h : D s₀ 5 t 0 s) :
    WP isa (.block unpack5Body) s fun s' => D s₀ 5 (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  have hl := hp.len_eq
  rw [hd] at hl
  have hB : (B s₀).length = 160 := by rw [hp.B_len, hd]
  have lb : ∀ i, ((B s₀).getD (5 * t + i) 0).toNat < 256 := fun i => byte_lt _
  have l0 := lb 0
  have l1 := lb 1
  have l2 := lb 2
  have l3 := lb 3
  have l4 := lb 4
  simp only [Nat.add_zero] at l0
  unfold unpack5Body
  refine ldW_spec 0 3 (by decide) (fun i => ((B s₀).getD (5 * t + i) 0).toNat) _ s _
    (fun i hi => by rw [Nat.zero_add]; exact h.byte hp (by omega)) fun s₁ o₁ v₁ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow] at v₁
  have h₁ := h.of_only o₁ (by decide)
  refine h₁.field hp hd ht (k := 0) (by decide) v₁ (sh := 0) (by decide) ?_ fun s₂ h₂ e₂ => ?_
  · rw [Nat.add_zero, decodeDecompress5_0 _ hB ht]; refine congrArg (decompress 5) ?_; omega
  refine h₂.field hp hd ht (k := 1) (by decide) ((congrArg BitVec.toNat (e₂)).trans v₁) (sh := 5) (by decide) ?_
    fun s₃ h₃ e₃ => ?_
  · rw [decodeDecompress5_1 _ hB ht]; refine congrArg (decompress 5) ?_; omega
  refine h₃.field hp hd ht (k := 2) (by decide) ((congrArg BitVec.toNat ((e₃).trans e₂)).trans v₁) (sh := 10) (by decide) ?_
    fun s₄ h₄ e₄ => ?_
  · rw [decodeDecompress5_2 _ hB ht]; refine congrArg (decompress 5) ?_; omega
  refine h₄.field hp hd ht (k := 3) (by decide) ((congrArg BitVec.toNat (((e₄).trans e₃).trans e₂)).trans v₁) (sh := 15) (by decide) ?_
    fun s₅ h₅ e₅ => ?_
  · rw [decodeDecompress5_3 _ hB ht]; refine congrArg (decompress 5) ?_; omega
  refine h₅.field hp hd ht (k := 4) (by decide) ((congrArg BitVec.toNat ((((e₅).trans e₄).trans e₃).trans e₂)).trans v₁) (sh := 20) (by decide) ?_
    fun s₆ h₆ e₆ => ?_
  · rw [decodeDecompress5_4 _ hB ht]; refine congrArg (decompress 5) ?_; omega
  refine h₆.field hp hd ht (k := 5) (by decide) ((congrArg BitVec.toNat (((((e₆).trans e₅).trans e₄).trans e₃).trans e₂)).trans v₁) (sh := 25) (by decide) ?_
    fun s₇ h₇ e₇ => ?_
  · rw [decodeDecompress5_5 _ hB ht]; refine congrArg (decompress 5) ?_; omega
  refine h₇.cross hp hd ht (k := 6) (by decide) ((congrArg BitVec.toNat ((((((e₇).trans e₆).trans e₅).trans e₄).trans e₃).trans e₂)).trans v₁) (sh := 30) (o := 4)
    (e := 3) (m := 2) (by decide) (by decide) (by decide) (by decide) (h₇.byte hp (o := 4) (by omega)) ?_ ?_
    fun s₈ h₈ _ => ?_
  · simp only [Nat.reducePow]; omega
  · rw [decodeDecompress5_6 _ hB ht]; refine congrArg (decompress 5) ?_; simp only [Nat.reducePow]; omega
  refine ldW_spec 4 0 (by decide) (fun i => ((B s₀).getD (5 * t + (4 + i)) 0).toNat) _ s₈ _
    (fun i hi => h₈.byte hp (by omega)) fun s₉ o₉ v₉ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero] at v₉
  refine (h₈.of_only o₉ (by decide)).field hp hd ht (k := 7) (by decide) v₉ (sh := 3) (by decide) ?_
    fun s₁₀ h₁₀ _ => next_spec ht h₁₀
  rw [decodeDecompress5_7 _ hB ht]; refine congrArg (decompress 5) ?_; omega

/-! ## `d` = 11: eight coefficients of eleven bytes -/

theorem step11 {s₀ : State} (hp : Pre s₀) (hd : dN s₀ = 11) {t : Nat} (ht : t < 32) {s : State}
    (h : D s₀ 11 t 0 s) :
    WP isa (.block unpack11Body) s fun s' => D s₀ 11 (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)) := by
  have hl := hp.len_eq
  rw [hd] at hl
  have hB : (B s₀).length = 352 := by rw [hp.B_len, hd]
  have lb : ∀ i, ((B s₀).getD (11 * t + i) 0).toNat < 256 := fun i => byte_lt _
  have l0 := lb 0
  have l1 := lb 1
  have l2 := lb 2
  have l3 := lb 3
  have l4 := lb 4
  have l5 := lb 5
  have l6 := lb 6
  have l7 := lb 7
  have l8 := lb 8
  have l9 := lb 9
  have l10 := lb 10
  simp only [Nat.add_zero] at l0
  unfold unpack11Body
  -- Bytes 0–3.
  refine ldW_spec 0 3 (by decide) (fun i => ((B s₀).getD (11 * t + i) 0).toNat) _ s _
    (fun i hi => by rw [Nat.zero_add]; exact h.byte hp (by omega)) fun s₁ o₁ v₁ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow] at v₁
  have h₁ := h.of_only o₁ (by decide)
  refine h₁.field hp hd ht (k := 0) (by decide) v₁ (sh := 0) (by decide) ?_ fun s₂ h₂ e₂ => ?_
  · rw [Nat.add_zero, decodeDecompress11_0 _ hB ht]; refine congrArg (decompress 11) ?_; omega
  refine h₂.field hp hd ht (k := 1) (by decide) ((congrArg BitVec.toNat (e₂)).trans v₁) (sh := 11) (by decide) ?_
    fun s₃ h₃ e₃ => ?_
  · rw [decodeDecompress11_1 _ hB ht]; refine congrArg (decompress 11) ?_; omega
  refine h₃.cross hp hd ht (k := 2) (by decide) ((congrArg BitVec.toNat ((e₃).trans e₂)).trans v₁) (sh := 22) (o := 4)
    (e := 1) (m := 10) (by decide) (by decide) (by decide) (by decide) (h₃.byte hp (o := 4) (by omega)) ?_ ?_
    fun s₄ h₄ _ => ?_
  · simp only [Nat.reducePow]; omega
  · rw [decodeDecompress11_2 _ hB ht]; refine congrArg (decompress 11) ?_; simp only [Nat.reducePow]; omega
  -- Bytes 4–7.
  refine ldW_spec 4 3 (by decide) (fun i => ((B s₀).getD (11 * t + (4 + i)) 0).toNat) _ s₄ _
    (fun i hi => h₄.byte hp (by omega)) fun s₅ o₅ v₅ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow, Nat.reduceAdd] at v₅
  have h₅ := h₄.of_only o₅ (by decide)
  refine h₅.field hp hd ht (k := 3) (by decide) v₅ (sh := 1) (by decide) ?_ fun s₆ h₆ e₆ => ?_
  · rw [decodeDecompress11_3 _ hB ht]; refine congrArg (decompress 11) ?_; omega
  refine h₆.field hp hd ht (k := 4) (by decide) ((congrArg BitVec.toNat (e₆)).trans v₅) (sh := 12) (by decide) ?_
    fun s₇ h₇ e₇ => ?_
  · rw [decodeDecompress11_4 _ hB ht]; refine congrArg (decompress 11) ?_; omega
  refine h₇.cross hp hd ht (k := 5) (by decide) ((congrArg BitVec.toNat ((e₇).trans e₆)).trans v₅) (sh := 23) (o := 8)
    (e := 2) (m := 9) (by decide) (by decide) (by decide) (by decide) (h₇.byte hp (o := 8) (by omega)) ?_ ?_
    fun s₈ h₈ _ => ?_
  · simp only [Nat.reducePow]; omega
  · rw [decodeDecompress11_5 _ hB ht]; refine congrArg (decompress 11) ?_; simp only [Nat.reducePow]; omega
  -- Bytes 8–10.
  refine ldW_spec 8 2 (by decide) (fun i => ((B s₀).getD (11 * t + (8 + i)) 0).toNat) _ s₈ _
    (fun i hi => h₈.byte hp (by omega)) fun s₉ o₉ v₉ => ?_
  simp only [pk, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceMul,
    Nat.reducePow, Nat.reduceAdd] at v₉
  have h₉ := h₈.of_only o₉ (by decide)
  refine h₉.field hp hd ht (k := 6) (by decide) v₉ (sh := 2) (by decide) ?_ fun s₁₀ h₁₀ e₁₀ => ?_
  · rw [decodeDecompress11_6 _ hB ht]; refine congrArg (decompress 11) ?_; omega
  refine h₁₀.field hp hd ht (k := 7) (by decide) ((congrArg BitVec.toNat (e₁₀)).trans v₉) (sh := 13) (by decide) ?_
    fun s₁₁ h₁₁ _ => next_spec ht h₁₁
  rw [decodeDecompress11_7 _ hB ht]; refine congrArg (decompress 11) ?_; omega

/-! ## The function -/

/-- After `ddInit5`. -/
structure Init (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = bP s₀
  edi : s.gpr .edi = fP s₀
  ev : eval .e s = some (decide (dN s₀ = 5))

theorem pub_esp {s₀ s₀' : State} (hq : Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

theorem init_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Init (.block ddInit5) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₀ := P0_argAddr s₀ 0
    have a₂ := P0_argAddr s₀ 2
    have a₃ := P0_argAddr s₀ 3
    have i₀ := P0_argIn (s₀ := s₀) (n := 4) (i := 0) (by omega) fit (by simp [hp.wr])
    have i₂ := P0_argIn (s₀ := s₀) (n := 4) (i := 2) (by omega) fit (by simp [hp.wr])
    have i₃ := P0_argIn (s₀ := s₀) (n := 4) (i := 3) (by omega) fit (by simp [hp.wr])
    have v₀ := P0_arg hp.sp (n := 4) (i := 0) (by omega) fit hp.stk_a
    have v₂ := P0_arg hp.sp (n := 4) (i := 2) (by omega) fit hp.stk_a
    have v₃ := P0_arg hp.sp (n := 4) (i := 3) (by omega) fit hp.stk_a
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a₀ a₂ a₃
    apply WP.of_runBlock
    simp (config := {decide := true}) only [ddInit5, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, a₂, a₃, i₀, i₂, i₃, v₀, v₂, v₃, ite_true, ite_false,
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
      (fun s₀ s => D s₀ b 0 0 s ∧ dN s₀ = d) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hd⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    ht
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp [h.edi], by simp,
    (by rw [h.mem]; exact Frame.refl _ _), fun j hj => absurd hj (by omega)⟩, hd⟩

theorem branch_piece {d : Nat} (body : List Instr)
    (hstep : ∀ t < 32, ∀ s₀ s, Pre s₀ → dN s₀ = d → D s₀ d t 0 s →
      WP isa (.block body) s fun s' => D s₀ d (t + 1) 0 s' ∧ eval .ne s' = some (decide (t + 1 < 32)))
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block body) hc).isSome = true)
    {hc' : Taint.Hint VG.X86.Taint.T}
    (ht' : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) hc').isSome = true) :
    Piece Pre Pub (fun s₀ s => Init s₀ s ∧ dN s₀ = d) Fin (countedLoop 32 body) :=
  (Piece.seq (ecx_piece d d ht') (Piece.countLoop (by decide) (fun t s₀ s => D s₀ d t 0 s ∧ dN s₀ = d)
    [.esp, .esi, .edi, .ecx]
    (fun t ht s₀ s hp ⟨h, hd⟩ => (hstep t ht s₀ s hp hd h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hd⟩, e⟩)
    (fun t _ s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.esi, h'.esi, bP, bP, hq.2.1]
      · rw [h.edi, h'.edi, fP, fP, hq.2.2.2.2]
      · rw [h.ecx, h'.ecx]) ht)).mono (fun _ _ _ h => h) fun _ _ _ ⟨h, _⟩ => h.fin

theorem ite_pub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
    decide (dN s₀ = 5) = decide (dN s₀' = 5) := fun _ _ _ _ hq => by rw [dN, dN, dV, dV, hq.2.2.2.1]

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block ddInit5) (.ite .e (countedLoop 32 unpack5Body) (countedLoop 32 unpack11Body))) := by
  refine Piece.seq init_piece (Piece.ite _ (fun _ _ _ h => h.ev) ite_pub ?_ ?_)
  · exact (branch_piece (d := 5) unpack5Body (fun t ht s₀ s hp hd h => step5 hp hd ht h) (by taint_decide)
      (by taint_decide)).mono (fun _ _ _ ⟨h, e⟩ => ⟨h, of_decide_eq_true e⟩) fun _ _ _ h => h
  · exact (branch_piece (d := 11) unpack11Body (fun t ht s₀ s hp hd h => step11 hp hd ht h) (by taint_decide)
      (by taint_decide)).mono
      (fun s₀ _ hp ⟨h, e⟩ => ⟨h, by
        have h5 := of_decide_eq_false e
        rcases mem_compressWidths1024 hp.d_mem with h' | h' <;> [exact absurd h' h5; exact h']⟩)
      fun _ _ _ h => h

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem1024.X86.decodeDecompress :=
  Piece.leaf (fun s₀ => [polyRegion (fA s₀)]) (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← hp.stk_eq]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `160`, `5` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5008 then 160 else if a = 0x500c then 5 else if a = 0x5011 then 4 else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.decodeDecompress
    (Spec.MlKem1024.decodeDecompressContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact polyIs_of_coeffAt fun i hi => hinv.coef i (by rw [n_eq] at hi; exact hi)
  · let st := satState satMem [⟨0, 160⟩] [⟨0x400, 1024⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem1024.X86.DecodeDecompress
