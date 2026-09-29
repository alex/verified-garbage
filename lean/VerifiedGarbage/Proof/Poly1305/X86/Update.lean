import VerifiedGarbage.Proof.Poly1305.X86.Buffer
import Mathlib.Tactic.NormNum.Basic

/-!
# Poly1305 on x86 (32-bit): `update`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : BitVec 32 := arg s₀ 3
abbrev dl : Nat := (arg s₀ 4).toNat
abbrev dR : Region := ⟨(dp s₀).setWidth 64, dl s₀⟩
abbrev scR : Region := ⟨(arg s₀ 5).setWidth 64, 128⟩
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem ((dp s₀).setWidth 64) c
end

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 32 := (arg s₀ 4).isLt

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, ⟨argAddr s₀ 0, 24⟩]
  wr : s₀.wr = [sR (stp s₀), scR s₀]
  st_d : (sR (stp s₀)).Disjoint (dR s₀)
  st_sc : (sR (stp s₀)).Disjoint (scR s₀)
  d_sc : (dR s₀).Disjoint (scR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 24⟩ (sR (stp s₀))
  arg_sc : Region.Disjoint ⟨argAddr s₀ 0, 24⟩ (scR s₀)
  ret_st : (retR s₀).Disjoint (sR (stp s₀))
  ret_sc : (retR s₀).Disjoint (scR s₀)
  st_fit : (stp s₀).toNat + 128 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + dl s₀ ≤ 2 ^ 32
  sc_fit : (arg s₀ 5).toNat + 128 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32

theorem UPre.of (s₀ : State) (h : Proof.Poly1305.updateX86.pre s₀) : UPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace UPre
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 24⟩, by rw [hp.rd]; simp, arg_contains (n := 24) (by have := hp.sp_fit; omega)
    (by omega)⟩

/-- An argument, in memory the code has written only in the state. -/
theorem arg_same {m : Mem} (hf : Frame [sR (stp s₀)] s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains (n := 24) (by have := hp.sp_fit; omega) (by omega)) (by simpa using hp.arg_st)
    (by decide)

theorem st_in : sR (stp s₀) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self

/-- Byte `c + i` of the data. -/
theorem data_addr {c i : Nat} (h : c + i < dl s₀) :
    addr (dp s₀ + BitVec.ofNat 32 c) i = (dp s₀).setWidth 64 + BitVec.ofNat 64 (c + i) := by
  have := hp.d_fit
  rw [show addr (dp s₀ + BitVec.ofNat 32 c) i = addr (dp s₀) (c + i) by
    simp only [addr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add], addr_eq (by omega)]

theorem dR_contains {i n : Nat} (h : i + n ≤ dl s₀) :
    (dR s₀).Contains ((dp s₀).setWidth 64 + BitVec.ofNat 64 i) n := by
  have := hp.d_fit
  simp only [Region.Contains]
  rw [show (dp s₀).setWidth 64 + BitVec.ofNat 64 i - (dp s₀).setWidth 64 = BitVec.ofNat 64 i by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h

/-- The data, as a source of bytes to copy. -/
theorem srcOk {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame [sR (stp s₀)] s₀.mem s.mem)
    {c n : Nat} (h : c + n ≤ dl s₀) (hn : 0 < n) :
    SrcOk s (stp s₀) s₀.mem (dp s₀ + BitVec.ofNat 32 c) n := by
  have := hp.d_fit
  refine ⟨?_, fun i hi => ⟨?_, fun hb => ?_, ?_⟩⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hrd, hwr, hp.rd, hp.data_addr (by omega)]
    exact ⟨dR s₀, by simp, hp.dR_contains (by omega)⟩
  · rw [hp.data_addr (by omega)] at hb
    exact hp.st_d _ (bfR_sub hp.st_fit _ hb) (hp.dR_contains (by omega))
  · rw [hp.data_addr (by omega)]
    exact hf _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hp.st_d _ hc (hp.dR_contains (by omega))

/-- The bytes at `dp + c`, as the data's. -/
theorem data_bytes {c n : Nat} (h : c + n ≤ dl s₀) :
    bytesAt s₀.mem ((dp s₀ + BitVec.ofNat 32 c).setWidth 64) n =
      bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have := hp.d_fit
    rw [show (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = addr (dp s₀) c from rfl, addr_eq (by omega)]

end UPre

theorem Dt_add (s₀ : State) (c n : Nat) :
    Dt s₀ (c + n) = Dt s₀ c ++ bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) n :=
  Poly1305.bytesAt_add _ _ _ _

/-! ## Invariants -/

/-- Before any data is consumed. -/
structure Pre1 (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends UCommon s₀ F s where
  esi : s.gpr .esi = dp s₀
  buf : bytesAt s.mem (bq (stp s₀)) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s.mem

/-- The buffer and the first `c` bytes of data are absorbed, a whole number
of blocks. -/
structure Cons (s₀ : State) (F : Nat → Nat) (c : Nat) (s : State) : Prop extends UCommon s₀ F s where
  c_le : c ≤ dl s₀
  whole : (kb s₀ + c) % 16 = 0
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  acc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s.mem

/-- The buffer and the data are the whole blocks `X`, absorbed, followed by
`Y`, in the buffer. -/
structure Done (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends UCommon s₀ F s where
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 (dl s₀)
  done : ∃ X Y : List Byte, Acc s₀ X s.mem ∧ X.length % 16 = 0 ∧ Y.length < 16 ∧
    Bf s₀ ++ Dt s₀ (dl s₀) = X ++ Y ∧ bytesAt s.mem (bq (stp s₀)) Y.length = Y

theorem Cons.regs {s₀ s s' : State} {F : Nat → Nat} {c : Nat} (h : Cons s₀ F c s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Cons s₀ F c s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    c_le := h.c_le, whole := h.whole, esi := hesi.trans h.esi, acc := hm ▸ h.acc }

theorem Done.regs {s₀ s s' : State} {F : Nat → Nat} (h : Done s₀ F s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Done s₀ F s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    esi := hesi.trans h.esi, done := hm ▸ h.done }

/-! ## Prologue -/

theorem uprologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (setup ++ [.mov .esi (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 8)),
      .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)])) s₀ fun s => ∃ F, SetupF s₀ F ∧
        Pre1 s₀ F s ∧ s.gpr .edx = BitVec.ofNat 32 (kb s₀) ∧
        s.zf = some (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by omega)) hfit hp.st_in)
    fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  have esp₁ := A₁.gpr .esp (by decide)
  have hF' := SetupF.of hF sv co
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 3)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by omega)) fun s₂ u₂ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, u₂.other _ (by decide), esp₁])
    (by rw [u₂.rd, u₂.wr, A₁.rd, A₁.wr]; exact hp.argIn (by omega)) fun s₃ u₃ _ => ?_
  refine wp_andx (readSrc_imm _ _) fun s₄ u₄ => wp_test fun s₅ k₅ z₅ => WP.block_nil ?_
  have hm : s₅.mem = s₁.mem := by rw [k₅.2.1, u₄.mem, u₃.mem, u₂.mem]
  have hedx₄ : s₄.gpr .edx = BitVec.ofNat 32 (kb s₀) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, hp.arg_same A₁.frame (i := 1) (by omega), and15]
  have hedx : s₅.gpr .edx = BitVec.ofNat 32 (kb s₀) := by rw [k₅.1 _ (by simp), hedx₄]
  have hw : ∀ k < 32, words s₅.mem (stp s₀) k = F k := fun k hk => by rw [hm]; exact A₁.words k hk
  refine ⟨F, hF', ⟨⟨c₁.keep (by rw [k₅.1 _ (by simp), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]) (by rw [k₅.2.2.2, u₄.wr, u₃.wr, u₂.wr]), ?_, by rw [hm]; exact A₁.frame,
      by rw [k₅.2.2.1, u₄.rd, u₃.rd, u₂.rd, A₁.rd], by rw [k₅.2.2.2, u₄.wr, u₃.wr, u₂.wr, A₁.wr],
      fun k hk _ _ => hw k hk⟩, ?_, ?_, fun hA => ?_⟩, hedx, ?_⟩
  · rw [k₅.1 _ (by simp), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
  · rw [k₅.1 _ (by simp), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      hp.arg_same A₁.frame (i := 3) (by omega)]
  · refine bytes_words hfit (fun k h₁ h₂ => ?_) (Nat.le_of_lt (kb_lt s₀))
    rw [hw k (by omega), hF'.low k (by omega) (by omega)]
  · exact acc_entry hfit hF' (fun k hk => hw k (by omega)) hA
  · rw [z₅, hedx₄]

/-! ## Filling the buffer -/

theorem Pre1.regs {s₀ s s' : State} {F : Nat → Nat} (h : Pre1 s₀ F s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pre1 s₀ F s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    esi := hesi.trans h.esi, buf := hm ▸ h.buf, acc := hm ▸ h.acc }

theorem sub16_eq {k : Nat} (hk : k ≤ 16) : (16 : BitVec 32) - BitVec.ofNat 32 k = BitVec.ofNat 32 (16 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (16 : BitVec 32).toNat = 16 from rfl]
  omega

theorem count_eq : count = .seq (.block [.mov .eax (.imm 16), .alu .sub .eax (.reg .edx),
    .mov .ecx (.mem (at_ .esp 20)), .alu .cmp .ecx (.reg .eax)])
    (.seq (.ite .b (.block [.mov .eax (.reg .ecx)]) (.block []))
      (.block [.alu .add .edx (.reg .edi), .alu .test .eax (.reg .eax)])) := rfl

/-- The number of bytes to copy, `n = min(16 - kb, dl)`, into `eax`, and the
address `state + kb` into `edx`. -/
theorem count_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State} (h : Pre1 s₀ F s)
    (hedx : s.gpr .edx = BitVec.ofNat 32 (kb s₀)) :
    WP isa count s fun s' => Pre1 s₀ F s' ∧ s'.gpr .edx = stp s₀ + BitVec.ofNat 32 (kb s₀) ∧
      s'.gpr .eax = BitVec.ofNat 32 (min (16 - kb s₀) (dl s₀)) ∧
      s'.zf = some (decide (min (16 - kb s₀) (dl s₀) = 0)) := by
  have hkl := kb_lt s₀
  have hdl : dl s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  rw [count_eq]
  refine WP.seq (wp_movi fun s₁ u₁ _ => wp_subx (readSrc_reg _ _) fun s₂ u₂ _ => ?_)
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 4))
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hp.argIn (by omega)) fun s₃ u₃ _ => ?_
  refine wp_cmpx (readSrc_reg _ _) fun s₄ k₄ _ cf₄ => WP.block_nil ?_
  have heax₂ : s₂.gpr .eax = BitVec.ofNat 32 (16 - kb s₀) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hedx, sub16_eq (by omega)]
  have hecx₃ : s₃.gpr .ecx = arg s₀ 4 := by
    rw [u₃.gpr, u₂.mem, u₁.mem]; exact hp.arg_same h.frame (by omega)
  have hP₄ : Pre1 s₀ F s₄ := h.regs
    (by rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [k₄.2.1, u₃.mem, u₂.mem, u₁.mem]) (by rw [k₄.2.2.1, u₃.rd, u₂.rd, u₁.rd])
    (by rw [k₄.2.2.2, u₃.wr, u₂.wr, u₁.wr])
  have hedx₄ : s₄.gpr .edx = BitVec.ofNat 32 (kb s₀) := by
    rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hedx]
  have heax₄ : s₄.gpr .eax = BitVec.ofNat 32 (16 - kb s₀) := by rw [k₄.gpr', u₃.other _ (by decide), heax₂]
  have hecx₄ : s₄.gpr .ecx = arg s₀ 4 := by rw [k₄.gpr', hecx₃]
  -- `eax = n`.
  refine WP.seq (WP.mono (Q := fun s₅ : State => Pre1 s₀ F s₅ ∧ s₅.gpr .edx = BitVec.ofNat 32 (kb s₀) ∧
      s₅.gpr .eax = BitVec.ofNat 32 (min (16 - kb s₀) (dl s₀))) ?_ fun s₅ ⟨hP₅, hedx₅, heax₅⟩ => ?_)
  · refine WP.ite (decide (dl s₀ < 16 - kb s₀)) (by
      simp only [eval, cf₄, u₃.other .eax (by decide), heax₂, hecx₃, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 - kb s₀ < 2 ^ 32 by omega)]) (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₅ u₅ _ => WP.block_nil ⟨hP₄.regs (u₅.other _ (by decide)) (u₅.other _ (by decide))
        (u₅.other _ (by decide)) u₅.mem u₅.rd u₅.wr, by rw [u₅.other _ (by decide), hedx₄], ?_⟩
      simp only [decide_eq_true_eq] at hb
      rw [u₅.gpr, hecx₄, Nat.min_eq_right (by omega)]
      simp
    · refine WP.block_nil ⟨hP₄, hedx₄, ?_⟩
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      rw [heax₄, Nat.min_eq_left hb]
  · refine wp_addx (readSrc_reg _ _) fun s₆ u₆ _ => wp_test fun s₇ k₇ z₇ => WP.block_nil ?_
    refine ⟨hP₅.regs (by rw [k₇.gpr', u₆.other _ (by decide)]) (by rw [k₇.gpr', u₆.other _ (by decide)])
      (by rw [k₇.gpr', u₆.other _ (by decide)]) (by rw [k₇.2.1, u₆.mem]) (by rw [k₇.2.2.1, u₆.rd])
      (by rw [k₇.2.2.2, u₆.wr]), ?_, ?_, ?_⟩
    · rw [k₇.gpr', u₆.gpr, hedx₅, hP₅.ctx.edi, BitVec.add_comm]
    · rw [k₇.gpr', u₆.other _ (by decide), heax₅]
    · rw [z₇, u₆.other _ (by decide), heax₅, BitVec.and_self, ofNat32_beq_zero (by omega)]

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (F : Nat → Nat) (n : Nat) (s : State) : Prop extends UCommon s₀ F s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 n
  buf : bytesAt s.mem (bq (stp s₀)) (kb s₀ + n) = Bf s₀ ++ Dt s₀ n
  acc : Acc s₀ [] s.mem

theorem UPre.srcOk0 {s₀ : State} (hp : UPre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [sR (stp s₀)] s₀.mem s.mem) {n : Nat} (h : n ≤ dl s₀) (hn : 0 < n) :
    SrcOk s (stp s₀) s₀.mem (dp s₀) n := by
  have := hp.srcOk hrd hwr hf (c := 0) (n := n) (by omega) hn
  simpa using this

theorem copyFill_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State} (h : Pre1 s₀ F s) {n : Nat}
    (hn : n ≤ dl s₀) (hn' : kb s₀ + n ≤ 16) (hedx : s.gpr .edx = stp s₀ + BitVec.ofNat 32 (kb s₀))
    (heax : s.gpr .eax = BitVec.ofNat 32 n) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) copyIn) s fun s' =>
      Filled s₀ F n s' ∧ s'.gpr .edx = stp s₀ + BitVec.ofNat 32 (kb s₀ + n) := by
  have hfit := hp.st_fit
  refine WP.ite (decide (n = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil ⟨{ h.toUCommon with
      n_le := hn, n_le' := hn', esi := by rw [h.esi]; simp
      buf := by rw [Nat.add_zero, h.buf]; simp [Dt, bytesAt]
      acc := h.acc }, by rw [hedx, Nat.add_zero]⟩
  · simp only [decide_eq_false_iff_not] at h0
    refine WP.mono (copy_ok (m₀ := s₀.mem) hfit hn' (by omega) (by rw [h.wr]; exact hp.st_in)
      (hp.srcOk0 h.rd h.wr h.frame hn (by omega)) h.esi hedx heax) fun s' hc => ?_
    have hf := hc.frame hn'
    have hU : UCommon s₀ F s' := h.toUCommon.buf (hc.keep _ (by decide) (by decide) (by decide) (by decide))
      (hc.keep _ (by decide) (by decide) (by decide) (by decide)) hf hc.rd hc.wr hfit
    exact ⟨{ hU with
      n_le := hn, n_le' := hn', esi := hc.esi
      buf := by rw [hc.buf hn', h.buf]
      acc := h.acc.words fun k hk => words_bf hfit hf (by omega) (by omega) }, hc.edx⟩

/-- Absorbing the full buffer. -/
theorem absorbBuf_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State} {n : Nat}
    (h : Filled s₀ F n s) (hfull : kb s₀ + n = 16) : WP isa (.block (absorbAt .edi 56 1)) s (Cons s₀ F n) := by
  have hfit := hp.st_fit
  have hc := h.ctx
  refine WP.mono (absorbAtFull_ok hc (bp := stp s₀ + BitVec.ofNat 32 56) (absorbBuf_okList 1)
    (fun h => absurd h (by decide)) (by decide) (fun k _ => by rw [hc.edi, buf_ea])
    (fun k hk => by rw [← buf_ea]; exact hc.inRW (by omega) (by omega))
    (fun k _ => .inr (by rw [← buf_ea]; congr 1; omega)) (by decide) (C := A0 s₀ < P)
    (fun hA => ⟨hF.coefs.congr fun k h₁ h₂ => h.keep k (by omega) (not_hS (.inl ⟨by omega, h₂⟩)) (.inr h₁),
      (h.acc hA).1⟩))
    fun s' ⟨S, ha⟩ => ?_
  refine ⟨⟨hc.keep (S.gpr _ (by decide)) S.wr, by rw [S.gpr _ (by decide)]; exact h.esp,
    h.frame.trans S.frame, by rw [S.rd]; exact h.rd, by rw [S.wr]; exact h.wr,
    fun k hk hS h' => (S.same k hk hS).trans (h.keep k hk hS h')⟩, h.n_le, by rw [hfull],
    by rw [S.gpr _ (by decide)]; exact h.esi, fun hA => ?_⟩
  obtain ⟨-, hv⟩ := h.acc hA
  obtain ⟨h4, hv'⟩ := ha hA
  refine ⟨h4, ?_⟩
  have hl : (Bf s₀ ++ Dt s₀ n).length = 16 := by
    simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; omega
  have e : leNum (Bf s₀ ++ Dt s₀ n ++ [0x01]) = leNum (Bf s₀ ++ Dt s₀ n) + 2 ^ 128 * 1 := by
    rw [Poly1305.leNum_append, hl]; rfl
  rw [Poly1305.absorbAll_nil] at hv
  rw [hv', buf_value hfit, ← hfull, h.buf, show (1 : BitVec 32).toNat = 1 from rfl, mod_step hv,
    Poly1305.absorbAll_block (by omega) (by omega), e]

theorem Filled.regs {s₀ s s' : State} {F : Nat → Nat} {n : Nat} (h : Filled s₀ F n s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Filled s₀ F n s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    n_le := h.n_le, n_le' := h.n_le', esi := hesi.trans h.esi, buf := hm ▸ h.buf,
    acc := hm ▸ h.acc }

theorem sub_self_add (st : BitVec 32) (a : Nat) : st + BitVec.ofNat 32 a - st = BitVec.ofNat 32 a := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State} (h : Pre1 s₀ F s)
    (hedx : s.gpr .edx = BitVec.ofNat 32 (kb s₀)) :
    WP isa fill s fun s' => (∃ c, Cons s₀ F c s') ∨ Done s₀ F s' := by
  have hkl := kb_lt s₀
  have hn : min (16 - kb s₀) (dl s₀) ≤ dl s₀ := Nat.min_le_right _ _
  have hn' : kb s₀ + min (16 - kb s₀) (dl s₀) ≤ 16 := by
    have := Nat.min_le_left (16 - kb s₀) (dl s₀); omega
  refine WP.seq (WP.mono (count_ok hp h hedx) fun s₁ ⟨h₁, hedx₁, heax₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (copyFill_ok hp h₁ hn hn' hedx₁ heax₁ hz₁) fun s₂ ⟨h₂, hedx₂⟩ => ?_)
  refine WP.seq (wp_subx (readSrc_reg _ _) fun s₃ u₃ _ => wp_cmpx (readSrc_imm _ _) fun s₄ k₄ z₄ _ =>
    WP.block_nil ?_)
  have h₄ : Filled s₀ F (min (16 - kb s₀) (dl s₀)) s₄ := h₂.regs
    (by rw [k₄.gpr', u₃.other _ (by decide)]) (by rw [k₄.gpr', u₃.other _ (by decide)])
    (by rw [k₄.gpr', u₃.other _ (by decide)]) (by rw [k₄.2.1, u₃.mem]) (by rw [k₄.2.2.1, u₃.rd])
    (by rw [k₄.2.2.2, u₃.wr])
  refine WP.ite (decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16))
    (by simp only [eval, z₄, u₃.gpr, hedx₂, h₂.ctx.edi, sub_self_add]; rw [eq16_beq hn'])
    (fun hfull => ?_) (fun hnf => ?_)
  · exact WP.mono (absorbBuf_ok hp hF h₄ (by simpa using hfull)) fun s' h' => .inl ⟨_, h'⟩
  · simp only [decide_eq_false_iff_not] at hnf
    have hnd : min (16 - kb s₀) (dl s₀) = dl s₀ := by omega
    refine WP.block_nil (.inr { h₄.toUCommon with
      esi := by rw [h₄.esi, hnd]
      done := ⟨[], Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)), h₄.acc, rfl, ?_, ?_, ?_⟩ })
    · simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; omega
    · rw [hnd, List.nil_append]
    · simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]
      exact h₄.buf

/-! ## Whole blocks of data -/

namespace UPre
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Word `d` of the data from byte `c` on, within the data. -/
theorem blk_sub {c d : Nat} (h : c + d + 4 ≤ dl s₀) :
    Region.Sub (sub (dp s₀ + BitVec.ofNat 32 c) d 4) (dR s₀) := fun a ha =>
  (hp.dR_contains (i := c + d) (n := 4) (by omega)).byte (by
    rw [← hp.data_addr (by omega)]; simp only [Region.Contains] at ha; omega)

theorem blkIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {c : Nat} (hc : c + 16 ≤ dl s₀)
    (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c) : BlkIn s := fun d hd => by
  rw [hrd, hwr, hesi, hp.rd, hp.data_addr (by omega)]
  exact ⟨dR s₀, by simp, hp.dR_contains (by omega)⟩

theorem blk_disj {c : Nat} (hc : c + 16 ≤ dl s₀) {k : Nat} (hk : k < 4) :
    (sub (dp s₀ + BitVec.ofNat 32 c) (4 * k) 4).Disjoint (sR (stp s₀)) :=
  hp.st_d.symm.sub_left (hp.blk_sub (by omega))

/-- The value of the block of data at byte `c`, with the `0x01` byte appended:
its four words and `2¹²⁸`. -/
theorem data_value {m : Mem} (hf : Frame [sR (stp s₀)] s₀.mem m) {c : Nat} (hc : c + 16 ≤ dl s₀) :
    blkv m (dp s₀ + BitVec.ofNat 32 c) 1 =
      leNum (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) 16 ++ [0x01]) := by
  have hw : ∀ k < 4, wv m (dp s₀ + BitVec.ofNat 32 c) (4 * k) =
      w32 s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) k := fun k hk => by
    show (wd m _ (4 * k)).toNat = _
    rw [wd_frame hf (by simpa using hp.blk_disj hc hk)]
    simp only [wd, w32]
    rw [hp.data_addr (by omega), add_ofNat_add]
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_bytesAt_16, ← hw 0 (by omega),
    ← hw 1 (by omega), ← hw 2 (by omega), ← hw 3 (by omega)]
  simp only [blkv, Spec.Poly1305.leNum]
  norm_num

end UPre

theorem left_eq : left = [.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.mem (at_ .esp 20)),
    .alu .add .eax (.reg .ecx), .alu .sub .eax (.reg .esi)] := rfl

theorem sub_left_eq {d : BitVec 32} {L c : Nat} (hL : L < 2 ^ 32) (hc : c ≤ L) :
    d + BitVec.ofNat 32 L - (d + BitVec.ofNat 32 c) = BitVec.ofNat 32 (L - c) := by
  apply BitVec.eq_of_toNat_eq
  have := d.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The length of the data left, `dl - c`, into `eax`. -/
theorem left_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State} (hU : UCommon s₀ F s) {c : Nat}
    (hc : c ≤ dl s₀) (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c) :
    WP isa (.block left) s fun s' => Keeps [.eax, .ecx] s s' ∧
      s'.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) ∧ s'.zf = some (decide (dl s₀ - c = 0)) := by
  have hdl : dl s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  rw [left_eq]
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 3)) (by rw [ea_at, hU.esp])
    (by rw [hU.rd, hU.wr]; exact hp.argIn (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 4)) (by rw [ea_at, u₁.other _ (by decide), hU.esp])
    (by rw [u₁.rd, u₁.wr, hU.rd, hU.wr]; exact hp.argIn (by omega)) fun s₂ u₂ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₃ u₃ _ => wp_subx (readSrc_reg _ _) fun s₄ u₄ z₄ => WP.block_nil ?_
  have heax₃ : s₃.gpr .eax = dp s₀ + BitVec.ofNat 32 (dl s₀) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, hp.arg_same hU.frame (i := 3) (by omega),
      hp.arg_same hU.frame (i := 4) (by omega)]
    simp
  have hesi₃ : s₃.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesi]
  have heax₄ : s₄.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) := by
    rw [u₄.gpr, heax₃, hesi₃, sub_left_eq hdl hc]
  refine ⟨⟨fun r hr => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩, heax₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other r hr.1, u₃.other r hr.1, u₂.other r hr.2, u₁.other r hr.1]
  · rw [z₄, ← u₄.gpr, heax₄, ofNat32_beq_zero (by omega)]

theorem add_ofNat_inj {d : BitVec 32} {a b L : Nat} (ha : a ≤ L) (hb : b ≤ L) (hL : L < 2 ^ 32)
    (h : d + BitVec.ofNat 32 a = d + BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := d.isLt
  omega

theorem Pos.whole {s₀ s : State} {F : Nat → Nat} (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) :
    ∃ c, c ≤ dl s₀ ∧ s.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
  rcases h with ⟨c, hc⟩ | hd
  · exact ⟨c, hc.c_le, hc.esi⟩
  · exact ⟨dl s₀, (Nat.le_refl _), hd.esi⟩

/-- One whole block of data. -/
theorem whole_step {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {c : Nat} {s : State}
    (h : Cons s₀ F c s) (hc : 16 ≤ dl s₀ - c) :
    WP isa (.block (absorb 1 ++ [.alu .add .esi (.imm 16)] ++ left ++ [.alu .cmp .eax (.imm 16)])) s fun s' =>
      Cons s₀ F (c + 16) s' ∧ s'.cf = some (decide (dl s₀ - (c + 16) < 16)) := by
  have hfit := hp.st_fit
  rw [show absorb 1 ++ [.alu .add .esi (.imm 16)] ++ left ++ [.alu .cmp .eax (.imm 16)] =
    absorb 1 ++ (.alu .add .esi (.imm 16) :: (left ++ [.alu .cmp .eax (.imm 16)])) by simp]
  refine WP.block_append (WP.mono (absorbFull_ok h.ctx (hp.blkIn h.rd h.wr (by omega) h.esi)
    (fun k hk => by rw [h.esi]; exact hp.blk_disj (by omega) hk) 1 (by decide) (C := A0 s₀ < P)
    (fun hA => ⟨hF.coefs.congr fun k h₁ h₂ => h.keep k (by omega) (not_hS (.inl ⟨by omega, h₂⟩)) (.inr h₁),
      (h.acc hA).1⟩)) fun s₁ ⟨S₁, h₁⟩ => ?_)
  refine wp_addx (readSrc_imm _ _) fun s₂ u₂ _ => ?_
  have hC₂ : Cons s₀ F (c + 16) s₂ := by
    refine ⟨⟨h.ctx.keep (by rw [u₂.other _ (by decide), S₁.gpr _ (by decide)]) (by rw [u₂.wr, S₁.wr]),
      by rw [u₂.other _ (by decide), S₁.gpr _ (by decide)]; exact h.esp,
      by rw [u₂.mem]; exact h.frame.trans S₁.frame, by rw [u₂.rd, S₁.rd]; exact h.rd,
      by rw [u₂.wr, S₁.wr]; exact h.wr,
      fun k hk hS h' => by rw [u₂.mem]; exact (S₁.same k hk hS).trans (h.keep k hk hS h')⟩,
      by omega, by have := h.whole; omega, ?_, fun hA => ?_⟩
    · rw [u₂.gpr, S₁.gpr _ (by decide), h.esi, BitVec.add_assoc,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
    · obtain ⟨h4, hv⟩ := h₁ hA
      obtain ⟨-, hv₀⟩ := h.acc hA
      refine ⟨by rw [u₂.mem]; exact h4, ?_⟩
      have h16 : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
        simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact h.whole
      have hb1 : 0 < (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) 16).length := by
        rw [Poly1305.length_bytesAt]; omega
      have hb2 : (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) 16).length ≤ 16 := by
        rw [Poly1305.length_bytesAt]
      rw [u₂.mem, hv, h.esi, show (1 : BitVec 32).toNat = 1 from rfl, hp.data_value h.frame (by omega),
        mod_step hv₀, Dt_add, ← List.append_assoc, Poly1305.absorbAll_append h16,
        Poly1305.absorbAll_block hb1 hb2]
  refine WP.block_append (WP.mono (left_ok hp hC₂.toUCommon hC₂.c_le hC₂.esi) fun s₃ ⟨k₃, heax₃, _⟩ => ?_)
  refine wp_cmpx (readSrc_imm _ _) fun s₄ k₄ _ cf₄ => WP.block_nil ⟨hC₂.regs
    (by rw [k₄.gpr', k₃.gpr']) (by rw [k₄.gpr', k₃.gpr']) (by rw [k₄.gpr', k₃.gpr'])
    (by rw [k₄.2.1, k₃.2.1]) (by rw [k₄.2.2.1, k₃.2.2.1]) (by rw [k₄.2.2.2, k₃.2.2.2]), ?_⟩
  rw [cf₄, heax₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := dl_lt s₀; omega)]
  rfl

/-- The loop over the whole blocks of data. -/
theorem whole_loop {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {c : Nat} {s : State}
    (h : Cons s₀ F c s) (hc : 16 ≤ dl s₀ - c) :
    WP isa (.loop (.block (absorb 1 ++ [.alu .add .esi (.imm 16)] ++ left ++ [.alu .cmp .eax (.imm 16)])) .ae) s
      fun s' => ∃ c', Cons s₀ F c' s' ∧ dl s₀ - c' < 16 := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = dl s₀ - c ∧ Cons s₀ F c s ∧ 16 ≤ dl s₀ - c) ?_ _ s
    ⟨c, rfl, h, hc⟩
  rintro k s ⟨c, rfl, h, hc⟩
  refine WP.mono (whole_step hp hF h hc) fun s' ⟨h', hcf⟩ => ?_
  by_cases hl : dl s₀ - (c + 16) < 16
  · exact .inl ⟨by simp [eval, hcf, hl], c + 16, h', hl⟩
  · exact .inr ⟨by simp [eval, hcf, hl], _, by omega, c + 16, rfl, h', by omega⟩

theorem whole_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) :
    WP isa whole s fun s' => (∃ c, Cons s₀ F c s' ∧ dl s₀ - c < 16) ∨ Done s₀ F s' := by
  obtain ⟨c, hcl, hesi⟩ := Pos.whole h
  have hU : UCommon s₀ F s := by rcases h with ⟨_, hc⟩ | hd; exacts [hc.toUCommon, hd.toUCommon]
  refine WP.seq (WP.mono (Q := fun s₂ : State => Keeps [.eax, .ecx] s s₂ ∧ s₂.cf = some (decide (dl s₀ - c < 16)))
    (WP.block_append (WP.mono (left_ok hp hU hcl hesi) fun s₁ ⟨k₁, heax₁, _⟩ =>
      wp_cmpx (readSrc_imm _ _) fun s₂ k₂ _ cf₂ => WP.block_nil ⟨(k₁.trans k₂).mono, ?_⟩))
    fun s₂ ⟨k₂, cf₂⟩ => ?_)
  · rw [cf₂, heax₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := dl_lt s₀; omega)]; rfl
  refine WP.ite (decide (dl s₀ - c < 16)) (by simp only [eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ?_
    rcases h with ⟨c', hc⟩ | hd
    · have e : c' = c := by
        have := hc.esi; rw [hesi] at this
        exact (add_ofNat_inj hcl hc.c_le (dl_lt s₀) this).symm
      subst e
      exact .inl ⟨c', hc.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2, hb⟩
    · exact .inr (hd.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2)
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    rcases h with ⟨c', hc⟩ | hd
    · have e : c' = c := by
        have := hc.esi; rw [hesi] at this
        exact (add_ofNat_inj hcl hc.c_le (dl_lt s₀) this).symm
      subst e
      exact WP.mono (whole_loop hp hF (hc.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2) hb)
        fun s' h' => .inl h'
    · have := hd.esi; rw [hesi] at this
      have := add_ofNat_inj hcl (Nat.le_refl _) (dl_lt s₀) this
      omega

/-! ## The rest of the data -/

/-- All the data consumed, into whole blocks. -/
theorem Cons.done {s₀ s : State} {F : Nat → Nat} {c : Nat} (h : Cons s₀ F c s) (hc : c = dl s₀) :
    Done s₀ F s :=
  { h.toUCommon with
    esi := by rw [h.esi, hc]
    done := ⟨Bf s₀ ++ Dt s₀ c, [], h.acc,
      by simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact h.whole, by simp,
      by rw [hc, List.append_nil], rfl⟩ }

theorem rest_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State}
    (h : (∃ c, Cons s₀ F c s ∧ dl s₀ - c < 16) ∨ Done s₀ F s) :
    WP isa rest s (Done s₀ F) := by
  have hfit := hp.st_fit
  obtain ⟨c, hcl, hesi⟩ : ∃ c, c ≤ dl s₀ ∧ s.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
    rcases h with ⟨c, hc, _⟩ | hd
    · exact ⟨c, hc.c_le, hc.esi⟩
    · exact ⟨dl s₀, (Nat.le_refl _), hd.esi⟩
  have hU : UCommon s₀ F s := by rcases h with ⟨_, hc, _⟩ | hd; exacts [hc.toUCommon, hd.toUCommon]
  refine WP.seq (WP.mono (Q := fun s₂ : State => Keeps [.eax, .ecx] s s₂ ∧
      s₂.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) ∧ s₂.zf = some (decide (dl s₀ - c = 0)))
    (WP.block_append (WP.mono (left_ok hp hU hcl hesi) fun s₁ ⟨k₁, heax₁, _⟩ =>
      wp_test fun s₂ k₂ z₂ => WP.block_nil ⟨(k₁.trans k₂).mono, by rw [k₂.gpr']; exact heax₁, ?_⟩))
    fun s₂ ⟨k₂, heax₂, z₂⟩ => ?_)
  · rw [z₂, heax₁, BitVec.and_self, ofNat32_beq_zero (by have := dl_lt s₀; omega)]
  refine WP.ite (decide (dl s₀ - c = 0)) (by simp only [eval, z₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ?_
    rcases h with ⟨c', hc, _⟩ | hd
    · have e : c' = c := add_ofNat_inj hc.c_le hcl (dl_lt s₀) (hc.esi.symm.trans hesi)
      subst e
      exact (hc.regs k₂.gpr' k₂.gpr' k₂.gpr' k₂.2.1 k₂.2.2.1 k₂.2.2.2).done (by have := hc.c_le; omega)
    · exact hd.regs k₂.gpr' k₂.gpr' k₂.gpr' k₂.2.1 k₂.2.2.1 k₂.2.2.2
  · simp only [decide_eq_false_iff_not] at hb
    rcases h with ⟨c', hc, hlt⟩ | hd
    · have e : c' = c := add_ofNat_inj hc.c_le hcl (dl_lt s₀) (hc.esi.symm.trans hesi)
      subst e
      have hc₂ := hc.regs k₂.gpr' k₂.gpr' k₂.gpr' k₂.2.1 k₂.2.2.1 k₂.2.2.2
      refine WP.seq (wp_mov fun s₃ u₃ _ => WP.block_nil ?_)
      have hc₃ := hc₂.regs (u₃.other _ (by decide)) (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.mem
        u₃.rd u₃.wr
      refine WP.mono (copy_ok (m₀ := s₀.mem) (j0 := 0) (n := dl s₀ - c') hfit (by omega) (by omega)
        (by rw [hc₃.wr]; exact hp.st_in)
        (hp.srcOk hc₃.rd hc₃.wr hc₃.frame (c := c') (n := dl s₀ - c') (by omega) (by omega)) hc₃.esi
        (by rw [u₃.gpr, hc₂.ctx.edi]; simp) (by rw [u₃.other _ (by decide), heax₂])) fun s' hcp => ?_
      have hf := hcp.frame (by omega)
      have hU' : UCommon s₀ F s' := hc₃.toUCommon.buf (hcp.keep _ (by decide) (by decide) (by decide) (by decide))
        (hcp.keep _ (by decide) (by decide) (by decide) (by decide)) hf hcp.rd hcp.wr hfit
      have hY : (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c') (dl s₀ - c')).length = dl s₀ - c' :=
        Poly1305.length_bytesAt _ _ _
      refine { hU' with
        esi := by rw [hcp.esi, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hc.c_le]
        done := ⟨Bf s₀ ++ Dt s₀ c', bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c') (dl s₀ - c'),
          hc₃.acc.words fun k hk => words_bf hfit hf (by omega) (by omega), ?_, by omega, ?_, ?_⟩ }
      · simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact hc.whole
      · rw [List.append_assoc, ← Dt_add, Nat.add_sub_cancel' hc.c_le]
      · have hb' := hcp.buf (by omega)
        rw [Nat.zero_add, hp.data_bytes (by omega)] at hb'
        rw [hY, hb']
        rfl
    · have := add_ofNat_inj (Nat.le_refl _) hcl (dl_lt s₀) (hd.esi.symm.trans hesi)
      omega

/-! ## Epilogue -/

theorem uepilogue_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (hd : Done s₀ F s) :
    WP isa (.block (reduce ++ restore)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.updateX86.post s₀ s' := by
  have hfit := hp.st_fit
  refine WP.mono (finish_ok hd.ctx) fun s₂ ⟨b₂, si₂, di₂, bp₂, sp₂, _, _, fr₂, z₂, hk₂, _, hr₂⟩ => ?_
  have hframe : Frame [sR (stp s₀)] s₀.mem s₂.mem := hd.frame.trans fr₂
  refine ⟨abi_of hF.saved ?_ ?_ ?_ ?_ (by rw [sp₂, hd.esp]) ?_, fun key msg hbuf hcnt => ?_⟩
  · rw [b₂, hd.keep 29 (by omega) (by decide) (by omega)]
  · rw [si₂, hd.keep 30 (by omega) (by decide) (by omega)]
  · rw [di₂, hd.keep 31 (by omega) (by decide) (by omega)]
  · rw [bp₂, hd.keep 5 (by omega) (by decide) (by omega)]
  · exact hframe.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · obtain ⟨W, rfl, hrep⟩ := buffered_split hfit hbuf (count_mod16 hcnt)
    obtain ⟨X, Y, hacc, hX, hY, hXY, hbufY⟩ := hd.done
    have hA := A0_lt hrep
    obtain ⟨hcl, hac⟩ := repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hacc hA
    rw [show W ++ Bf s₀ ++ bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat = W ++ X ++ Y by
      rw [List.append_assoc, show bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat = Dt s₀ (dl s₀)
        from rfl, hXY, List.append_assoc]]
    refine Buffered.of ⟨?_, ?_, ?_⟩ hY ?_
    · rw [List.length_append]; have := hrep.1; omega
    · rw [key_same hfit fun k h₁ h₂ => ?_]
      · exact hrep.2.1
      · rw [hk₂ k (by omega) (not_hS (.inl ⟨by omega, by omega⟩)) (by omega),
          hd.keep k (by omega) (not_hS (.inl ⟨by omega, by omega⟩)) (by omega), hF.low k (by omega) (by omega)]
    · rw [leNum_acc hfit (words_ok _ _), z₂, hcl, Poly1305.accumulate_append hrep.1, hac, hr₂ h4, hv,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
      simp
    · rw [← bq_eq hfit, bytes_words hfit (fun k h₁ h₂ => hk₂ k (by omega)
        (by simp only [hS, List.mem_cons, List.not_mem_nil, or_false]; omega) (by omega)) (by omega), hbufY]

/-! ## The whole function -/

theorem update_eq : update = .seq (.block (setup ++ [.mov .esi (.mem (at_ .esp 16)),
    .mov .edx (.mem (at_ .esp 8)), .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)]))
    (.seq (.ite .e (.block []) fill) (.seq whole (.seq rest (.block (reduce ++ restore))))) := rfl

/-- Nothing buffered: nothing of the data is consumed yet. -/
theorem Pre1.cons {s₀ s : State} {F : Nat → Nat} (h : Pre1 s₀ F s) (hk : kb s₀ = 0) : Cons s₀ F 0 s :=
  { h.toUCommon with
    c_le := Nat.zero_le _, whole := by rw [hk]
    esi := by rw [h.esi]; simp
    acc := by
      have e : Bf s₀ ++ Dt s₀ 0 = [] := by simp only [Bf, Dt, hk]; rfl
      rw [e]; exact h.acc }

theorem update_correct {s₀ : State} (hp : UPre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.updateX86.post s₀ s' := by
  rw [update_eq]
  refine WP.seq (WP.mono (uprologue_ok hp) fun s₁ ⟨F, hF, h₁, hedx, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s : State => (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0) (by simp [eval, hz])
      (fun h => ?_) (fun _ => fill_ok hp hF h₁ hedx)
    rw [BitVec.and_self, ofNat32_beq_zero (by have := kb_lt s₀; omega)] at h
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil (.inl ⟨0, h₁.cons h⟩)
  refine WP.seq (WP.mono (whole_ok hp hF h₂) fun s₃ h₃ => ?_)
  exact WP.seq (WP.mono (rest_ok hp h₃) fun s₄ h₄ => uepilogue_ok hp hF h₄)

/-! ## Constant time and satisfiability -/

/-- The taint analysis starts with the stack arguments public. -/
def updateτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 28 }

theorem update_wf₀ {s : State} (hp : UPre s) : VG.X86.Taint.Wf updateτ₀ s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [updateτ₀]; omega, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.arg_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_sc hp.arg_sc

theorem update_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.updateX86.pre s₁)
    (h₂ : Proof.Poly1305.updateX86.pre s₂) (hpub : Proof.Poly1305.updateX86.pub s₁ s₂) :
    VG.X86.Taint.Agree updateτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := UPre.of _ h₁; have hp₂ := UPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, update_wf₀ hp₁, update_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega))
      h4 hk⟩
  simp only [updateτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
  subst hr; exact hesp

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def updateSatMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4011 then 0x20 else if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := updateSatMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 24⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 128⟩]

theorem updateSat_pre : Proof.Poly1305.updateX86.pre updateSat := by
  have a0 : arg updateSat 0 = 0x1000 := by decide
  have a3 : arg updateSat 3 = 0x2000 := by decide
  have a4 : arg updateSat 4 = 0 := by decide
  have a5 : arg updateSat 5 = 0x3000 := by decide
  have e : argAddr updateSat 0 = 0x4004 := by decide
  simp only [Proof.Poly1305.updateX86, a0, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, updateSat] at h₁ h₂
    bv_omega

theorem update_verified : Verified X86.target update Proof.Poly1305.updateX86 :=
  ⟨fun s hs => update_correct (UPre.of s hs),
    VG.Taint.constantTime (A := taint) updateτ₀ (fun _ _ h₁ h₂ hp => update_agree₀ h₁ h₂ hp)
      (by taint_decide),
    ⟨updateSat, updateSat_pre⟩⟩

end VG.Proof.Poly1305.X86
