import VerifiedGarbage.Proof.Poly1305.X86_64.Buffer

/-!
# Poly1305 on x86-64: `update`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_mov32i wp_cmp wp_test wp_addi wp_subi)
open VG.Proof.Sha3 (ofNat_succ sub_ofNat ofNat_beq_zero)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : Addr := s₀.gpr .rdx
abbrev dl : Nat := (s₀.gpr .rcx).toNat
abbrev dR : Region := ⟨dp s₀, dl s₀⟩
/-- The number of bytes buffered. -/
abbrev kb : Nat := (s₀.gpr .rsi).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kb s₀)
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c
end

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : sR (st s₀) ∈ s₀.wr
  st_d : (sR (st s₀)).Disjoint (dR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))

theorem UPre.of (s₀ : State) (h : Proof.Poly1305.updateX86_64.pre s₀) : UPre s₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by omega)

theorem Bf_length (s₀ : State) : (Bf s₀).length = kb s₀ := Poly1305.length_bytesAt _ _ _

theorem rcx_eq (s₀ : State) : s₀.gpr .rcx = BitVec.ofNat 64 (dl s₀) := by simp

theorem dR_contains (s₀ : State) {i n : Nat} (h : i + n ≤ dl s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 i) n := by
  have := dl_lt s₀
  simp only [Region.Contains]
  rw [show dp s₀ + BitVec.ofNat 64 i - dp s₀ = BitVec.ofNat 64 i by bv_omega, toNat_ofNat_lt (by omega)]
  exact h

/-! ## Invariants -/

/-- What holds throughout. -/
structure UCommon (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r8 : s.gpr .r8 = R0 s₀
  r9 : s.gpr .r9 = R1 s₀
  r10 : (s.gpr .r10).toNat = 5 * ((R1 s₀).toNat / 4)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [wR (st s₀)] s₀.mem s.mem
  saved : Saved (st s₀) s₀ s.mem

/-- The accumulator in `r11, rbx, rbp` is that of the message on entry
followed by the whole blocks `X`. -/
def Acc (s₀ : State) (X : List Byte) (s : State) : Prop :=
  H2 s₀ ≤ 4 → hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) X % P ∧ (s.gpr .rbp).toNat ≤ 4

/-- Before any data is consumed. -/
structure Pre1 (s₀ : State) (s : State) : Prop extends UCommon s₀ s where
  rsi : s.gpr .rsi = dp s₀
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s

/-- The buffer and the first `c` bytes of data are absorbed, a whole number
of blocks. -/
structure Cons (s₀ : State) (c : Nat) (s : State) : Prop extends UCommon s₀ s where
  c_le : c ≤ dl s₀
  whole : (kb s₀ + c) % 16 = 0
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 c
  rcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - c)
  acc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s

/-- The buffer and the data are the whole blocks `X`, absorbed, followed by
`Y`, in the buffer. -/
structure Done (s₀ : State) (s : State) : Prop extends UCommon s₀ s where
  done : ∃ X Y : List Byte, Acc s₀ X s ∧ X.length % 16 = 0 ∧ Y.length < 16 ∧
    Bf s₀ ++ Dt s₀ (dl s₀) = X ++ Y ∧ bytesAt s.mem (off (st s₀) 56) Y.length = Y

theorem UCommon.of_regs {s₀ s s' : State} (h : UCommon s₀ s)
    (hg : ∀ r ∈ [Reg.rdi, .rsp, .r8, .r9, .r10], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : UCommon s₀ s' where
  rdi := by rw [hg _ (by simp)]; exact h.rdi
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  r8 := by rw [hg _ (by simp)]; exact h.r8
  r9 := by rw [hg _ (by simp)]; exact h.r9
  r10 := by rw [hg _ (by simp)]; exact h.r10
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Writing the buffer keeps what holds throughout. -/
theorem UCommon.of_buf {s₀ s s' : State} (h : UCommon s₀ s)
    (hg : ∀ r ∈ [Reg.rdi, .rsp, .r8, .r9, .r10], s'.gpr r = s.gpr r)
    (hm : Frame [bfR (st s₀)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : UCommon s₀ s' where
  rdi := by rw [hg _ (by simp)]; exact h.rdi
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  r8 := by rw [hg _ (by simp)]; exact h.r8
  r9 := by rw [hg _ (by simp)]; exact h.r9
  r10 := by rw [hg _ (by simp)]; exact h.r10
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  frame := h.frame.trans (hm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wR (st s₀), List.mem_singleton_self _, bfR_sub_wR _⟩)
  saved := h.saved.of_frame hm

theorem Acc.of_regs {s₀ s s' : State} {X : List Byte} (h : Acc s₀ X s)
    (hg : ∀ r ∈ [Reg.r11, .rbx, .rbp], s'.gpr r = s.gpr r) : Acc s₀ X s' := by
  intro hH
  obtain ⟨h1, h2⟩ := h hH
  simp only [hval, hg .r11 (by simp), hg .rbx (by simp), hg .rbp (by simp)]
  exact ⟨h1, h2⟩

/-- A state that differs from `s` only in the flags. -/
def FlagsOnly (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem UCommon.flags {s₀ s s' : State} (h : UCommon s₀ s) (hf : FlagsOnly s s') : UCommon s₀ s' :=
  h.of_regs (fun r _ => by rw [hf.1]) hf.2.1 hf.2.2.1 hf.2.2.2

theorem Acc.flags {s₀ s s' : State} {X : List Byte} (h : Acc s₀ X s) (hf : FlagsOnly s s') : Acc s₀ X s' :=
  h.of_regs fun r _ => by rw [hf.1]

theorem Cons.flags {s₀ s s' : State} {c : Nat} (h : Cons s₀ c s) (hf : FlagsOnly s s') : Cons s₀ c s' :=
  { h.toUCommon.flags hf with
    c_le := h.c_le, whole := h.whole, rsi := by rw [hf.1]; exact h.rsi, rcx := by rw [hf.1]; exact h.rcx,
    acc := h.acc.flags hf }

theorem Done.flags {s₀ s s' : State} (h : Done s₀ s) (hf : FlagsOnly s s') : Done s₀ s' := by
  obtain ⟨X, Y, a, b, c, d, e⟩ := h.done
  exact { h.toUCommon.flags hf with done := ⟨X, Y, a.flags hf, b, c, d, by rw [hf.2.1]; exact e⟩ }

/-- Bytes of data read from memory the code has written only in the working space. -/
theorem UPre.data {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame [wR (st s₀)] s₀.mem m) {i : Nat}
    (hi : i < dl s₀) : m (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  hf.bytes (R := dR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.st_d.symm.sub_right (sub_sR _ (by omega))) (show dl s₀ ≤ 2 ^ 64 by have := dl_lt s₀; omega) hi

/-- The source of a copy from the data. -/
theorem UPre.srcOk {s₀ : State} (hp : UPre s₀) {s : State} (hc : UCommon s₀ s) {c n : Nat}
    (h : c + n ≤ dl s₀) : SrcOk s s₀.mem (dp s₀ + BitVec.ofNat 64 c) n := by
  intro i hi
  have e : dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i = dp s₀ + BitVec.ofNat 64 (c + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine ⟨⟨dR s₀, by rw [hc.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    dR_contains s₀ (by omega)⟩, fun hb => ?_, hp.data hc.frame (by omega)⟩
  rw [hc.rdi] at hb
  exact hp.st_d _ (sub_sR _ (by omega) _ hb) (dR_contains s₀ (by omega))

theorem UCommon.in_st {s₀ : State} (hp : UPre s₀) {s : State} (h : UCommon s₀ s) :
    sR (s.gpr .rdi) ∈ s.wr := by
  rw [h.wr, h.rdi]; exact hp.wr

/-! ## Prologue -/

set_option simprocs false in
theorem kInit_ok (s : State) :
    WP isa (.block [.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15), .mov .rsi (.reg .rdx),
      .alu .test .r12 (.reg .r12)]) s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) ∧ s'.gpr .rsi = s.gpr .rdx ∧
      s'.zf = some (BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) &&&
        BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) == 0) ∧
      Keeps [.r12, .rsi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', and15]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem uprologue_eq : save ++ setup ++ [.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15),
    .mov .rsi (.reg .rdx), .alu .test .r12 (.reg .r12)] = save ++ (setup ++ [.mov .r12 (.reg .rsi),
    .alu .and .r12 (.imm 15), .mov .rsi (.reg .rdx), .alu .test .r12 (.reg .r12)]) := by
  simp only [List.append_assoc]

theorem uprologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup ++ [.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15),
      .mov .rsi (.reg .rdx), .alu .test .r12 (.reg .r12)])) s₀ fun s =>
      Pre1 s₀ s ∧ s.gpr .rcx = s₀.gpr .rcx ∧
        s.zf = some (BitVec.ofNat 64 (kb s₀) &&& BitVec.ofNat 64 (kb s₀) == 0) := by
  rw [uprologue_eq]
  refine WP.block_append (WP.mono (save_ok s₀ hp.wr) fun s₁ ⟨g₁, rd₁, wr₁, _, _, f₁, sv₁⟩ => ?_)
  refine WP.block_append (WP.mono (setup_ok s₁ (by
    rw [wr₁, g₁]; exact List.mem_append_right _ hp.wr))
    fun s₂ ⟨e8, e9, e10, e11, e12, e13, k₂⟩ => ?_)
  refine WP.mono (kInit_ok s₂) fun s₃ ⟨c12, csi, cz, k₃⟩ => ?_
  have hm : Mem₁ s₀ s₁.mem := ⟨f₁, sv₁⟩
  rw [g₁, hm.readW_low (by omega)] at e8 e9 e11 e12 e13
  have k := k₂.trans k₃
  have g : ∀ r, r ∉ [Reg.rax, .r8, .r9, .r10, .r11, .rbx, .rbp, .r12, .rsi] → s₃.gpr r = s₀.gpr r :=
    fun r hr => by rw [k.1 r (by simpa using hr), g₁]
  have hrsi₂ : s₂.gpr .rsi = s₀.gpr .rsi := by rw [k₂.gpr' (r := .rsi), g₁]
  have hrdx₂ : s₂.gpr .rdx = s₀.gpr .rdx := by rw [k₂.gpr' (r := .rdx), g₁]
  have hm₃ : s₃.mem = s₁.mem := by rw [k.2.1]
  refine ⟨⟨⟨g .rdi (by decide), g .rsp (by decide), ?_, ?_, ?_, by rw [k.2.2.1, rd₁], by rw [k.2.2.2, wr₁],
    by rw [hm₃]; exact hm.frame_wR, by rw [hm₃]; exact sv₁⟩, ?_, ?_, ?_, fun hH2 => ?_⟩,
    g .rcx (by decide), ?_⟩
  · rw [k₃.gpr' (r := .r8), e8]
  · rw [k₃.gpr' (r := .r9), e9]
  · rw [k₃.gpr' (r := .r10), e10, e9]
  · rw [csi, hrdx₂]
  · rw [c12, hrsi₂]
  · rw [hm₃]
    have := kb_lt s₀
    refine bytesAt_frame f₁ (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact buf_disjoint_svR _ (by omega)
  · simp only [hval, k₃.gpr' (r := .r11), k₃.gpr' (r := .rbx), k₃.gpr' (r := .rbp), e11, e12, e13]
    refine ⟨?_, hH2⟩
    rw [Poly1305.absorbAll_nil, A0, leNum_acc]
  · rw [cz, hrsi₂]

/-- Nothing buffered: nothing of the data is consumed yet. -/
theorem Pre1.cons {s₀ s : State} (h : Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) (hk : kb s₀ = 0) :
    Cons s₀ 0 s :=
  { h.toUCommon with
    c_le := Nat.zero_le _, whole := by rw [hk]
    rsi := by rw [h.rsi]; simp
    rcx := by rw [hrcx]; simp
    acc := by
      have e : Bf s₀ ++ Dt s₀ 0 = [] := by simp only [Bf, Dt, hk]; rfl
      rw [e]; exact h.acc }

/-! ## Filling the buffer -/


/-- `Pre1` is kept by changes to `rax`, `rcx` and the flags. -/
theorem Pre1.of_regs {s₀ s s' : State} (h : Pre1 s₀ s) (hg : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pre1 s₀ s' :=
  { h.toUCommon.of_regs (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) hm hrd hwr with
    rsi := by rw [hg _ (by decide) (by decide)]; exact h.rsi
    r12 := by rw [hg _ (by decide) (by decide)]; exact h.r12
    buf := by rw [hm]; exact h.buf
    acc := h.acc.of_regs fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) }

/-- The number of bytes to copy, `n = min(16 - kb, dl)`, into `rax`, and
`dl - n` into `rcx`. -/
theorem count_ok {s₀ : State} {s : State} (h : Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa (.seq (.block [.mov32 .rax (.imm 16), .alu .sub .rax (.reg .r12), .alu .cmp .rcx (.reg .rax)])
      (.seq (.ite .b (.block [.mov .rax (.reg .rcx)]) (.block []))
        (.block [.alu .sub .rcx (.reg .rax), .alu .test .rax (.reg .rax)]))) s fun s' =>
      Pre1 s₀ s' ∧ s'.gpr .rax = BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀)) ∧
        s'.gpr .rcx = BitVec.ofNat 64 (dl s₀ - min (16 - kb s₀) (dl s₀)) ∧
        s'.zf = some (decide (min (16 - kb s₀) (dl s₀) = 0)) := by
  have hkl := kb_lt s₀
  have hdl := dl_lt s₀
  have e16 : BitVec.setWidth 64 (16 : BitVec 32) - BitVec.ofNat 64 (kb s₀) =
      BitVec.ofNat 64 (16 - kb s₀) := by
    rw [show BitVec.setWidth 64 (16 : BitVec 32) = BitVec.ofNat 64 16 by decide, sub_ofNat (by omega)]
  refine WP.seq (wp_mov32i fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (16 - kb s₀) := by
    rw [u₂.gpr, u₁.other .r12 (by decide), h.r12, u₁.gpr, e16]
  have hrcx₂ : s₂.gpr .rcx = s₀.gpr .rcx := by
    rw [u₂.other .rcx (by decide), u₁.other .rcx (by decide), hrcx]
  have hrax₃ : s₃.gpr .rax = BitVec.ofNat 64 (16 - kb s₀) := by rw [g₃, hrax₂]
  have hrcx₃ : s₃.gpr .rcx = s₀.gpr .rcx := by rw [g₃, hrcx₂]
  have hP₃ : Pre1 s₀ s₃ := h.of_regs (fun r h1 _ => by rw [g₃, u₂.other r h1, u₁.other r h1])
    (by rw [m₃, u₂.mem, u₁.mem]) (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  -- `rax = n`.
  refine WP.seq (WP.mono (Q := fun s₄ : State => Pre1 s₀ s₄ ∧ s₄.gpr .rcx = s₀.gpr .rcx ∧
      s₄.gpr .rax = BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀))) ?_ fun s₄ ⟨hP₄, hrcx₄, hrax₄⟩ => ?_)
  · refine WP.ite (decide (dl s₀ < 16 - kb s₀)) (by
      simp only [eval, cf₃, hrcx₂, hrax₂, toNat_ofNat_lt (show 16 - kb s₀ < 2 ^ 64 by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₄ u₄ => WP.block_nil ⟨hP₃.of_regs (fun r h1 _ => u₄.other r h1) u₄.mem u₄.rd u₄.wr,
        by rw [u₄.other _ (by decide), hrcx₃], ?_⟩
      simp only [decide_eq_true_eq] at hb
      rw [u₄.gpr, hrcx₃, Nat.min_eq_right (by omega), rcx_eq]
    · refine WP.block_nil ⟨hP₃, hrcx₃, ?_⟩
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      rw [hrax₃, Nat.min_eq_left hb]
  · refine wp_sub fun s₅ u₅ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_
    have hg : ∀ r, r ≠ .rcx → s₆.gpr r = s₄.gpr r := fun r hr => by rw [g₆, u₅.other r hr]
    refine ⟨hP₄.of_regs (fun r _ h2 => hg r h2) (by rw [m₆, u₅.mem]) (by rw [rd₆, u₅.rd])
      (by rw [wr₆, u₅.wr]), by rw [hg _ (by decide)]; exact hrax₄, ?_, ?_⟩
    · rw [g₆, u₅.gpr, hrcx₄, hrax₄, rcx_eq, sub_ofNat (by omega)]
    · rw [z₆, u₅.other _ (by decide), hrax₄, BitVec.and_self, ofNat_beq_zero (by omega)]

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (n : Nat) (s : State) : Prop extends UCommon s₀ s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - n)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀ + n)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀ + n) = Bf s₀ ++ Dt s₀ n
  acc : Acc s₀ [] s

theorem copyFill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s) {n : Nat} (hn : n ≤ dl s₀)
    (hn' : kb s₀ + n ≤ 16) (hrax : s.gpr .rax = BitVec.ofNat 64 n)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - n)) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) copyIn) s (Filled s₀ n) := by
  refine WP.ite (decide (n = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil { h.toUCommon with
      n_le := hn, n_le' := hn', rsi := by rw [h.rsi]; simp, rcx := hrcx, r12 := by rw [h.r12]; simp
      buf := by rw [Nat.add_zero, h.buf]; simp [Dt, bytesAt]
      acc := h.acc }
  · simp only [decide_eq_false_iff_not] at h0
    have hsrc := hp.srcOk h.toUCommon (c := 0) (n := n) (by omega)
    refine WP.mono (copy_ok (j0 := kb s₀) (by omega) (by omega) (h.toUCommon.in_st hp)
      hsrc (by rw [h.rsi]; simp) (by rw [h.r12]) hrax) fun s' hc => ?_
    have hc' : UCommon s₀ s' := h.toUCommon.of_buf (fun r hr => hc.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
      (by rw [← h.rdi]; exact hc.frame (by omega)) hc.rd hc.wr
    refine { hc' with
      n_le := hn, n_le' := hn', rsi := by rw [hc.rsi]; simp
      rcx := by rw [hc.keep _ (by decide) (by decide) (by decide) (by decide), hrcx]
      r12 := hc.r12
      buf := ?_
      acc := h.acc.of_regs fun r hr => hc.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) }
    have hb := hc.buf (by omega)
    rw [h.rdi, h.buf] at hb
    rw [hb]
    simp [Dt]

theorem se1' : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

/-- Absorbing the full buffer. -/
theorem absorbFull_ok {s₀ : State} (hp : UPre s₀) {s : State} {n : Nat} (h : Filled s₀ n s)
    (hfull : kb s₀ + n = 16) : WP isa (.block (absorbAt .rdi 56 1)) s (Cons s₀ n) := by
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  refine WP.mono (absorbBuf_ok s (pad := 1) (Or.inr rfl) (h.toUCommon.in_st hp) (q := (R1 s₀).toNat / 4)
    (by rw [h.r8]; exact r0_lt _) (by rw [h.r9]; omega) (by omega) (by rw [h.r10])) fun s' ⟨ha, k⟩ => ?_
  refine { h.toUCommon.of_regs (fun r hr => k.gpr' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) k.2.1 k.2.2.1 k.2.2.2 with
    c_le := h.n_le, whole := by rw [hfull]
    rsi := by rw [k.gpr' (r := .rsi)]; exact h.rsi
    rcx := by rw [k.gpr' (r := .rcx)]; exact h.rcx
    acc := fun hH2 => ?_ }
  obtain ⟨hv, hb⟩ := h.acc hH2
  obtain ⟨hv', hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  have hl : (Bf s₀ ++ Dt s₀ n).length = 16 := by
    simp only [List.length_append, Dt, Poly1305.length_bytesAt]; omega
  have hbuf : bytesAt s.mem (off (s.gpr .rdi) 56) 16 = Bf s₀ ++ Dt s₀ n := by
    rw [h.rdi]; rw [← hfull]; exact h.buf
  have e : leNum (Bf s₀ ++ Dt s₀ n ++ [0x01]) = leNum (Bf s₀ ++ Dt s₀ n) + 2 ^ 128 * 1 := by
    rw [Poly1305.leNum_append, hl]; rfl
  rw [Poly1305.absorbAll_nil] at hv
  rw [hv', hbuf, h.r8, h.r9, show (1 : BitVec 32).toNat = 1 from rfl, mod_step hv,
    Poly1305.absorbAll_block (by omega) (by omega), e]

theorem Filled.flags {s₀ s s' : State} {n : Nat} (h : Filled s₀ n s) (hf : FlagsOnly s s') :
    Filled s₀ n s' :=
  { h.toUCommon.flags hf with
    n_le := h.n_le, n_le' := h.n_le', rsi := by rw [hf.1]; exact h.rsi, rcx := by rw [hf.1]; exact h.rcx,
    r12 := by rw [hf.1]; exact h.r12, buf := by rw [hf.2.1]; exact h.buf, acc := h.acc.flags hf }

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa fill s fun s' => (∃ c, Cons s₀ c s') ∨ (Done s₀ s' ∧ s'.gpr .rcx = 0) := by
  have hkl := kb_lt s₀
  have hdl := dl_lt s₀
  have hn : min (16 - kb s₀) (dl s₀) ≤ dl s₀ := Nat.min_le_right _ _
  have hn' : kb s₀ + min (16 - kb s₀) (dl s₀) ≤ 16 := by
    have := Nat.min_le_left (16 - kb s₀) (dl s₀); omega
  refine WP.seq (WP.mono (count_ok h hrcx) fun s₁ ⟨h₁, hrax₁, hrcx₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (copyFill_ok hp h₁ hn hn' hrax₁ hrcx₁ hz₁) fun s₂ h₂ => ?_)
  refine WP.seq (wp_cmpi fun s₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_)
  have hf : FlagsOnly s₂ s₃ := ⟨g₃, m₃, rd₃, wr₃⟩
  have h₃ := h₂.flags hf
  refine WP.ite (decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16))
    (by simp only [eval, z₃, h₂.r12, se16']
        rw [VG.Proof.Sha3.sub_beq (a := kb s₀ + min (16 - kb s₀) (dl s₀)) (b := 16) (by omega) (by omega)])
    (fun hfull => ?_) (fun hnf => ?_)
  · exact WP.mono (absorbFull_ok hp h₃ (by simpa using hfull)) fun s' h' => .inl ⟨_, h'⟩
  · simp only [decide_eq_false_iff_not] at hnf
    have hnd : min (16 - kb s₀) (dl s₀) = dl s₀ := by omega
    refine WP.block_nil (.inr ⟨{ h₃.toUCommon with
      done := ⟨[], Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)), h₃.acc, rfl, ?_, ?_, ?_⟩ }, ?_⟩)
    · simp only [List.length_append, Dt, Poly1305.length_bytesAt]; omega
    · rw [hnd, List.nil_append]
    · simp only [List.length_append, Dt, Poly1305.length_bytesAt]
      exact h₃.buf
    · rw [h₃.rcx, hnd, Nat.sub_self]; rfl

/-! ## Whole blocks of data -/

/-- The data's words, as numbers: its bytes from `dp + c`. -/
theorem data_value {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame [wR (st s₀)] s₀.mem m) {c : Nat}
    (hc : c + 16 ≤ dl s₀) :
    word m (dp s₀ + BitVec.ofNat 64 c) 0 + 2 ^ 64 * word m (dp s₀ + BitVec.ofNat 64 c) 8 +
        2 ^ 128 * (1 : BitVec 32).toNat =
      leNum (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16 ++ [0x01]) := by
  have hw : ∀ d : Nat, d + 8 ≤ 16 → m.readW (dp s₀ + BitVec.ofNat 64 c + BitVec.ofInt 64 (d : Int)) 64 =
      s₀.mem.readW (dp s₀ + BitVec.ofNat 64 c + BitVec.ofInt 64 (d : Int)) 64 := by
    intro d hd
    have e : dp s₀ + BitVec.ofNat 64 c + BitVec.ofInt 64 (d : Int) = dp s₀ + BitVec.ofNat 64 (c + d) := by
      rw [ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [e]
    refine hf.readW (dR_contains s₀ (n := 64 / 8) (by omega)) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_d.symm.sub_right (sub_sR _ (by omega))
  simp only [word]
  rw [hw 0 (by omega), hw 8 (by omega), Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  have h2 : (1 : BitVec 32).toNat = 1 := rfl
  rw [h1, h2]
  simp only [off]
  omega

set_option simprocs false in
theorem advance16_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 16), .alu .cmp .rcx (.imm 16)]) s
      fun s' => s'.gpr .rsi = s.gpr .rsi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 16 ∧
        s'.cf = some (decide ((s.gpr .rcx - 16).toNat < 16)) ∧ Keeps [.rsi, .rcx] s s' := by
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ => wp_cmpi fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [g₃, u₂.other _ (by decide), u₁.gpr, se16]
  · rw [g₃, u₂.gpr, u₁.other _ (by decide), se16]
  · rw [cf₃, u₂.gpr, u₁.other _ (by decide), se16]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₃, u₂.other r hr.2, u₁.other r hr.1]
  · rw [m₃, u₂.mem, u₁.mem]
  · rw [rd₃, u₂.rd, u₁.rd]
  · rw [wr₃, u₂.wr, u₁.wr]

/-- One whole block of data. -/
theorem whole_step {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : Cons s₀ c s)
    (hc : 16 ≤ dl s₀ - c) :
    WP isa (.block (absorb 1 ++ [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 16),
      .alu .cmp .rcx (.imm 16)])) s fun s' =>
      Cons s₀ (c + 16) s' ∧ s'.cf = some (decide (dl s₀ - (c + 16) < 16)) := by
  have hdl := dl_lt s₀
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
    intro d hd
    rw [h.rd, h.rsi, hp.rd, ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀, List.mem_append_left _ (List.mem_singleton_self _), dR_contains s₀ (by omega)⟩
  refine WP.block_append (WP.mono (absorb_ok s (pad := 1) (Or.inr rfl) (q := (R1 s₀).toNat / 4)
    (by rw [h.r8]; exact r0_lt _) (by rw [h.r9]; omega) (by omega) (by rw [h.r10]) (hin 0 (by omega))
    (hin 8 (by omega))) fun s₁ ⟨ha, k₁⟩ => ?_)
  refine WP.mono (advance16_ok s₁) fun s₂ ⟨a₁, a₂, a₃, k₂⟩ => ?_
  have k := k₁.trans k₂
  have hrcx₁ : s₁.gpr .rcx = BitVec.ofNat 64 (dl s₀ - c) := by rw [k₁.gpr' (r := .rcx), h.rcx]
  have hrcx₂ : s₂.gpr .rcx = BitVec.ofNat 64 (dl s₀ - (c + 16)) := by
    rw [a₂, hrcx₁, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨{ h.toUCommon.of_regs (fun r hr => k.gpr' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) k.2.1 k.2.2.1 k.2.2.2 with
    c_le := by omega
    whole := by have := h.whole; omega
    rsi := by rw [a₁, k₁.gpr' (r := .rsi), h.rsi, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    rcx := hrcx₂
    acc := fun hH2 => ?_ }, ?_⟩
  · obtain ⟨hv, hb⟩ := h.acc hH2
    obtain ⟨hv', hb'⟩ := ha hb
    have hval₂ : hval s₂ = hval s₁ := by
      simp only [hval, k₂.gpr' (r := .r11), k₂.gpr' (r := .rbx), k₂.gpr' (r := .rbp)]
    refine ⟨?_, by rw [k₂.gpr' (r := .rbp)]; exact hb'⟩
    have h16 : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
      simp only [List.length_append, Dt, Poly1305.length_bytesAt]; exact h.whole
    have hb1 : 0 < (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16).length := by
      rw [Poly1305.length_bytesAt]; omega
    have hb2 : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16).length ≤ 16 := by
      rw [Poly1305.length_bytesAt]
    rw [hval₂, hv', h.rsi, data_value hp h.frame (by omega), h.r8, h.r9, mod_step hv,
      show Dt s₀ (c + 16) = Dt s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16 from
        Poly1305.bytesAt_add _ _ _ _, ← List.append_assoc, Poly1305.absorbAll_append h16,
      Poly1305.absorbAll_block hb1 hb2]
  · rw [a₃, hrcx₁, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, sub_ofNat (by omega),
      toNat_ofNat_lt (by omega), Nat.sub_sub]

/-- The loop over the whole blocks of data. -/
theorem whole_loop {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : Cons s₀ c s)
    (hc : 16 ≤ dl s₀ - c) :
    WP isa (.loop (.block (absorb 1 ++ [.alu .add .rsi (.imm 16), .alu .sub .rcx (.imm 16),
      .alu .cmp .rcx (.imm 16)])) .ae) s fun s' => ∃ c', Cons s₀ c' s' ∧ dl s₀ - c' < 16 := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = dl s₀ - c ∧ Cons s₀ c s ∧ 16 ≤ dl s₀ - c) ?_ _ s
    ⟨c, rfl, h, hc⟩
  rintro k s ⟨c, rfl, h, hc⟩
  refine WP.mono (whole_step hp h hc) fun s' ⟨h', hcf⟩ => ?_
  by_cases hl : dl s₀ - (c + 16) < 16
  · exact .inl ⟨by simp [eval, hcf, hl], c + 16, h', hl⟩
  · exact .inr ⟨by simp [eval, hcf, hl], _, by omega, c + 16, rfl, h', by omega⟩

theorem whole_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .rcx = 0)) :
    WP isa whole s fun s' => (∃ c, Cons s₀ c s' ∧ dl s₀ - c < 16) ∨ (Done s₀ s' ∧ s'.gpr .rcx = 0) := by
  have hdl := dl_lt s₀
  refine WP.seq (wp_cmpi fun s₁ g₁ m₁ rd₁ wr₁ cf₁ _ => WP.block_nil ?_)
  have hf : FlagsOnly s s₁ := ⟨g₁, m₁, rd₁, wr₁⟩
  refine WP.ite (decide ((s.gpr .rcx).toNat < 16)) (by simp only [eval, cf₁, se16']; rfl)
    (fun hb => ?_) (fun hb => ?_)
  · refine WP.block_nil ?_
    simp only [decide_eq_true_eq] at hb
    rcases h with ⟨c, hc⟩ | ⟨hd, hz⟩
    · rw [hc.rcx, toNat_ofNat_lt (by omega)] at hb
      exact .inl ⟨c, hc.flags hf, hb⟩
    · exact .inr ⟨hd.flags hf, by rw [g₁, hz]⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    rcases h with ⟨c, hc⟩ | ⟨hd, hz⟩
    · rw [hc.rcx, toNat_ofNat_lt (by omega)] at hb
      exact WP.mono (whole_loop hp (hc.flags hf) hb) fun s' h' => .inl h'
    · rw [hz] at hb; simp at hb

/-! ## The rest of the data -/

theorem rest_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, Cons s₀ c s ∧ dl s₀ - c < 16) ∨ (Done s₀ s ∧ s.gpr .rcx = 0)) :
    WP isa rest s (Done s₀) := by
  have hdl := dl_lt s₀
  refine WP.seq (wp_test fun s₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have hf : FlagsOnly s s₁ := ⟨g₁, m₁, rd₁, wr₁⟩
  refine WP.ite (s.gpr .rcx &&& s.gpr .rcx == 0) (by simp only [eval, z₁]) (fun hb => ?_) (fun hb => ?_)
  · refine WP.block_nil ?_
    rcases h with ⟨c, hc, _⟩ | ⟨hd, _⟩
    · rw [BitVec.and_self, hc.rcx, ofNat_beq_zero (by omega)] at hb
      simp only [decide_eq_true_eq] at hb
      have hcd : c = dl s₀ := by have := hc.c_le; omega
      refine { hc.toUCommon.flags hf with
        done := ⟨Bf s₀ ++ Dt s₀ c, [], (hc.acc.flags hf), ?_, by simp, by rw [hcd, List.append_nil], rfl⟩ }
      simp only [List.length_append, Dt, Poly1305.length_bytesAt]; exact hc.whole
    · exact hd.flags hf
  · rcases h with ⟨c, hc, hlt⟩ | ⟨hd, hz⟩
    · rw [BitVec.and_self, hc.rcx, ofNat_beq_zero (by omega)] at hb
      simp only [decide_eq_false_iff_not] at hb
      have hc₁ := hc.flags hf
      refine WP.seq (wp_mov32i fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
      have hg : ∀ r, r ≠ .rax → r ≠ .r12 → s₃.gpr r = s₁.gpr r := fun r h1 h2 => by
        rw [u₃.other r h1, u₂.other r h2]
      have hU₃ : UCommon s₀ s₃ := hc₁.toUCommon.of_regs (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
        (by rw [u₃.mem, u₂.mem]) (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr])
      have hsrc := hp.srcOk hU₃ (c := c) (n := dl s₀ - c) (by omega)
      refine WP.mono (copy_ok (j0 := 0) (by omega) (by omega) (hU₃.in_st hp) hsrc
        (by rw [hg _ (by decide) (by decide)]; exact hc₁.rsi) (by rw [u₃.other _ (by decide), u₂.gpr]; rfl)
        (by rw [u₃.gpr, u₂.other _ (by decide), hc₁.rcx])) fun s' hcp => ?_
      have hk : ∀ r, r ≠ .rsi → r ≠ .r12 → r ≠ .rax → r ≠ .r13 → s'.gpr r = s₁.gpr r :=
        fun r h1 h2 h3 h4 => by rw [hcp.keep r h1 h2 h3 h4, hg r h3 h2]
      have hU' : UCommon s₀ s' := hU₃.of_buf (fun r hr => hcp.keep r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
        (by rw [← hU₃.rdi]; exact hcp.frame (by omega)) hcp.rd hcp.wr
      have hY : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (dl s₀ - c)).length = dl s₀ - c :=
        Poly1305.length_bytesAt _ _ _
      refine { hU' with
        done := ⟨Bf s₀ ++ Dt s₀ c, bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (dl s₀ - c),
          hc₁.acc.of_regs fun r hr => hk r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide) (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide) (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide) (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl <;> decide), ?_, by omega, ?_, ?_⟩ }
      · simp only [List.length_append, Dt, Poly1305.length_bytesAt]; exact hc.whole
      · rw [List.append_assoc, show Dt s₀ (dl s₀) = Dt s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c)
          (dl s₀ - c) by rw [Dt, Dt, ← Poly1305.bytesAt_add]; congr 1; omega]
      · have hb' := hcp.buf (by omega)
        rw [hU₃.rdi, Nat.zero_add] at hb'
        rw [hY, hb']
        rfl
    · rw [hz] at hb; simp at hb

/-! ## Epilogue -/

theorem storeH_buf (m : Mem) (st : Addr) (h0 h1 h2 : BitVec 64) {n : Nat} (hn : n ≤ 16) :
    bytesAt (storeH m st h0 h1 h2) (off st 56) n = bytesAt m (off st 56) n := by
  have hf : Frame [hR st] m (storeH m st h0 h1 h2) := by
    have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c 0 (by omega))).writeW List.mem_cons_self _
      (c 8 (by omega))).writeW List.mem_cons_self _ (c 16 (by omega))
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  intro a h₁ h₂
  simp only [Region.Contains, off, ofInt_natCast] at h₁ h₂
  bv_omega

theorem uepilogue_ok {s₀ : State} (hp : UPre s₀) {s : State} (hd : Done s₀ s) :
    WP isa (.block (reduce ++ [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [k₁.gpr' (r := .rdi), hd.rdi]
  have hw : sR (s₁.gpr .rdi) ∈ s₁.wr := by rw [k₁.2.2.2, hd.wr, rdi₁]; exact hp.wr
  refine WP.mono (storeRestore_ok s₁ hw) fun s₂ ⟨m₂, g1, g2, g3, g4, g5, g6, g7⟩ => ?_
  rw [rdi₁, k₁.2.1] at m₂ g1 g2 g3 g4 g5 g6
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := hd.saved
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₂.mem := by
    rw [m₂]; exact storeH_frame (hd.frame.mono (by simp)) _ _ _
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hbuf hcnt => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, storeH_saved _ _ _ _ _ (by omega) (by omega), sv1]
    · rw [g2, storeH_saved _ _ _ _ _ (by omega) (by omega), sv2]
    · rw [g7, k₁.gpr' (r := .rsp), hd.rsp]
    · rw [g3, storeH_saved _ _ _ _ _ (by omega) (by omega), sv3]
    · rw [g4, storeH_saved _ _ _ _ _ (by omega) (by omega), sv4]
    · rw [g5, storeH_saved _ _ _ _ _ (by omega) (by omega), sv5]
    · rw [g6, storeH_saved _ _ _ _ _ (by omega) (by omega), sv6]
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    have hd' := hp.ret_st
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hd'.sub_right (Region.sub_prefix (by omega))
    · exact hd'.sub_right (sub_sR _ (by omega))
  · obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
    have hk : kb s₀ = (W ++ B).length % 16 := hcnt
    have hBf : Bf s₀ = B := by rw [Bf, hk, off_56, hBb]
    obtain ⟨X, Y, hacc, hX, hY, hXY, hbufY⟩ := hd.done
    obtain ⟨hlen, hkey, hA⟩ := hrep
    have hH2 := H2_le ⟨hlen, hkey, hA⟩
    obtain ⟨hv, hb⟩ := hacc hH2
    have hR := hr hb
    rw [← off_24] at hkey
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := hkey
    rw [List.append_assoc, ← Dt, ← hBf, hXY, ← List.append_assoc]
    refine Buffered.of ⟨?_, ?_, ?_⟩ hY ?_
    · rw [List.length_append]; omega
    · rw [← off_24, key_frame hf, hkey']
    · rw [m₂, storeH_acc, ← hkey', clamp_key, Poly1305.accumulate_append hlen]
      have hA' : accumulate (Rn s₀) W = A0 s₀ := by rw [A0, hA, ← hkey', clamp_key]
      rw [hA']
      change hval s₁ = _
      have hlt : A0 s₀ < P := by rw [← hA']; exact Poly1305.accumulate_lt _ _
      rw [hR, hv, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]
    · rw [← off_56, m₂, storeH_buf _ _ _ _ _ (by omega), hbufY]

/-! ## The whole function -/

theorem update_correct {s₀ : State} (hp : UPre s₀) :
    WP isa update s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (uprologue_ok hp) fun s₁ ⟨h₁, hrcx, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s : State => (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .rcx = 0)) ?_
    fun s₂ h₂ => ?_)
  · refine WP.ite (BitVec.ofNat 64 (kb s₀) &&& BitVec.ofNat 64 (kb s₀) == 0) (by simp [eval, hz])
      (fun h => ?_) (fun _ => fill_ok hp h₁ hrcx)
    rw [BitVec.and_self, ofNat_beq_zero (by have := kb_lt s₀; omega)] at h
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil (.inl ⟨0, h₁.cons hrcx h⟩)
  refine WP.seq (WP.mono (whole_ok hp h₂) fun s₃ h₃ => ?_)
  exact WP.seq (WP.mono (rest_ok hp h₃) fun s₄ h₄ => uepilogue_ok hp h₄)

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩]

theorem update_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.update Proof.Poly1305.updateX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := update_correct (UPre.of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨updateSat, rfl, List.mem_singleton_self _, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, updateSat] at h₁ h₂
      bv_omega

end VG.Proof.Poly1305.X86_64
