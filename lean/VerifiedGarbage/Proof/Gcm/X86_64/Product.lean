import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.X86_64.Ctmul

/-!
# GHASH on x86-64: running a word product

Untrusted: everything here is checked by Lean. `Impl.Gcm.X86_64.product`
leaves `prodVal` of its factors in `r14:r13` (`product_ok`), changing no
other register but `rax, rdx, rbx, rbp, r9–r12`, and not memory.
-/

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm.X86_64.Ctmul

/-- `s'` differs from `s` at most in the registers `clob` and the flags. -/
def Keeps (clob : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (clob : List Reg) (s : State) : Keeps clob s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {c : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps c s₁ s₂) (h₂ : Keeps c s₂ s₃) :
    Keeps c s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {c c' : List Reg} {s s' : State} (h : Keeps c s s') (hc : ∀ r ∈ c, r ∈ c') :
    Keeps c' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hc r h'), h.2⟩

/-- A load through a register the state keeps. -/
theorem Keeps.readSrc_mem {c : List Reg} {s s' : State} (h : Keeps c s s') {b : Reg} (hb : b ∉ c)
    (d : Nat) : readSrc s' (.mem (at_ b d)) = readSrc s (.mem (at_ b d)) := by
  simp only [readSrc, State.ea, at_, h.1 b hb]
  unfold State.load64
  rw [h.2.1, h.2.2.1, h.2.2.2]

/-- `mul` leaves the 128-bit product in `rdx:rax`. -/
theorem ofNat_split (p : Nat) : BitVec.ofNat 64 (p / 2 ^ 64) ++ BitVec.ofNat 64 p = BitVec.ofNat 128 p := by
  apply BitVec.eq_of_toNat_eq
  rw [Proof.Gcm.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## One product -/

/-- The registers one product changes. -/
abbrev termClob : List Reg := [.rax, .rdx, AL, AH]

set_option simprocs false in
theorem mulAcc_ok (d : Nat) (b : Reg) (hb : b ∉ termClob) (s : State) {c : BitVec 64}
    (hc : readSrc s (.mem (at_ .r8 d)) = some c) :
    WP isa (.block [.mov .rax (.mem (at_ .r8 d)), .mul b, .alu .xor AL (.reg .rax),
        .alu .xor AH (.reg .rdx)]) s fun s' =>
      s'.gpr AH ++ s'.gpr AL = (s.gpr AH ++ s.gpr AL) ^^^ ip c (s.gpr b) ∧ Keeps termClob s s' := by
  simp only [termClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  have hc' : s.load64 (s.ea (at_ .r8 d)) = some c := hc
  apply WP.of_runBlock
  simp only [AL, AH] at h3 h4 ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execMul, readSrc, hc', isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false, h1,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [← BitVec.xor_append, ofNat_split]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, AL, AH] at hr
    obtain ⟨r1, r2, r3, r4⟩ := hr
    simp only [r1, r2, r3, r4, ite_false]

theorem B_not_mem {j : Nat} : B j ∉ termClob ∧ B j ≠ PL ∧ B j ≠ PH ∧ B j ≠ .r8 ∧ B j ≠ W0 ∧
    B j ≠ .rsi ∧ B j ≠ .rdi ∧ B j ≠ .rcx ∧ B j ≠ .rsp := by
  unfold B; split <;> decide

theorem B_inj : ∀ i < 4, ∀ j < 4, B i = B j → i = j := by decide

/-- The table of `hv` is at `q`. -/
def Tbl (s : State) (q : Nat) (hv : BitVec 64) : Prop :=
  ∀ t < 8, readSrc s (.mem (at_ .r8 (off (8 * q + t)))) = some (part hv t)

theorem Tbl.keeps {c : List Reg} {s s' : State} {q : Nat} {hv : BitVec 64} (h : Tbl s q hv)
    (hk : Keeps c s s') (hc : Reg.r8 ∉ c) : Tbl s' q hv :=
  fun t ht => (hk.readSrc_mem hc _).trans (h t ht)

/-- The classes of `yv` are in the registers `B j`. -/
def Bs (s : State) (yv : BitVec 64) : Prop := ∀ j < 4, s.gpr (B j) = yv &&& cls j

theorem Bs.keeps {c : List Reg} {s s' : State} {yv : BitVec 64} (h : Bs s yv) (hk : Keeps c s s')
    (hc : ∀ j < 4, B j ∉ c) : Bs s' yv :=
  fun j hj => (hk.1 _ (hc j hj)).trans (h j hj)

/-! ## One class -/

/-- The registers a class changes. -/
abbrev clsClob : List Reg := [.rax, .rdx, AL, AH, PL, PH]

theorem term_ok {q k t : Nat} (ht : t < 8) {hv yv : BitVec 64} {s : State} (hT : Tbl s q hv)
    (hB : Bs s yv) :
    WP isa (.block (term q k t)) s fun s' =>
      s'.gpr AH ++ s'.gpr AL = (s.gpr AH ++ s.gpr AL) ^^^ ip (part hv t) (yv &&& cls (jOf k t)) ∧
      Keeps termClob s s' := by
  have hj : jOf k t < 4 := Nat.mod_lt _ (by omega)
  refine WP.mono (mulAcc_ok _ (B (jOf k t)) B_not_mem.1 s (hT t ht)) fun s' ⟨h1, h2⟩ => ⟨?_, h2⟩
  rw [h1, hB _ hj]

set_option simprocs false in
theorem zero_ok {lo hi : Reg} (h : lo ≠ hi) (s : State) :
    WP isa (.block [.mov lo (.imm 0), .mov hi (.imm 0)]) s fun s' =>
      s'.gpr hi ++ s'.gpr lo = (0 : BitVec 128) ∧ Keeps [lo, hi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    isa, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', h]
  refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

set_option simprocs false in
theorem mask_ok (k : Nat) (s : State) :
    WP isa (.block [.movImm64 .rax (cls k), .alu .and AL (.reg .rax), .alu .and AH (.reg .rax),
        .alu .xor PL (.reg AL), .alu .xor PH (.reg AH)]) s fun s' =>
      s'.gpr PH ++ s'.gpr PL = (s.gpr PH ++ s.gpr PL) ^^^ ((s.gpr AH ++ s.gpr AL) &&& (cls k ++ cls k)) ∧
      Keeps clsClob s s' := by
  apply WP.of_runBlock
  simp only [AL, AH, PL, PH]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [← BitVec.xor_append, ← BitVec.and_append], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [clsClob, AL, AH, PL, PH, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, -, r3, r4, r5, r6⟩ := hr
  simp only [r1, r3, r4, r5, r6, ite_false]

theorem clsCode_ok {q k : Nat} {hv yv : BitVec 64} {s : State} (hT : Tbl s q hv)
    (hB : Bs s yv) :
    WP isa (.block (clsCode q k)) s fun s' =>
      s'.gpr PH ++ s'.gpr PL = (s.gpr PH ++ s.gpr PL) ^^^ (classSum hv yv k 8 &&& (cls k ++ cls k)) ∧
      Keeps clsClob s s' := by
  rw [clsCode, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok (by decide) s) fun s₁ ⟨hz, hk₁⟩ => ?_
  have hT₁ := hT.keeps hk₁ (by decide)
  have hB₁ := hB.keeps hk₁ fun j _ => by
    have := (B_not_mem (j := j)).1
    simp only [termClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.2.2.1, this.2.2.2⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun t s' => s'.gpr AH ++ s'.gpr AL = classSum hv yv k t ∧ Keeps termClob s₁ s')
    (fun t s' ht ⟨h₁, h₂⟩ => WP.mono (term_ok ht (hT₁.keeps h₂ (by decide))
      (hB₁.keeps h₂ fun j _ => B_not_mem.1)) fun s'' ⟨h₃, h₄⟩ =>
        ⟨by rw [h₃, h₁, classSum_succ], h₂.trans h₄⟩)
    8 le_rfl s₁ ⟨hz, Keeps.refl _ _⟩) fun s₂ ⟨h₁, h₂⟩ => ?_
  refine WP.mono (mask_ok k s₂) fun s₃ ⟨h₃, h₄⟩ => ⟨?_, ?_⟩
  · have hk : Keeps termClob s s₂ := (hk₁.mono (by decide)).trans h₂
    rw [h₃, h₁, hk.1 PL (by decide), hk.1 PH (by decide)]
  · exact ((hk₁.mono (by decide)).trans (h₂.mono (by decide))).trans h₄


/-! ## The product -/

/-- The registers the classes of the second factor are in. -/
abbrev Bregs : List Reg := [.rbx, .rbp, .r9, .r10]

/-- The registers a product changes. -/
abbrev prodClob : List Reg := [.rax, .rdx, .rbx, .rbp, .r9, .r10, AL, AH, PL, PH]

theorem B_mem (j : Nat) : B j ∈ Bregs := by unfold B; split <;> decide

theorem Keeps.setReg {c : List Reg} {s s' : State} (h : Keeps c s s') {r : Reg} (hr : r ∈ c)
    (v : BitVec 64) : Keeps c s (s'.setReg r v) :=
  ⟨fun r' hr' => by
    simp only [State.setReg]
    rw [ite_eq_right (fun (h' : r' = r) => hr' (h' ▸ hr))]
    exact h.1 r' hr', h.2⟩

set_option simprocs false in
theorem andCls_ok (b : Reg) (m : BitVec 64) (y : Src) (s : State) {yv : BitVec 64}
    (hy : ∀ v, readSrc (s.setReg b v) y = some yv) :
    WP isa (.block [.movImm64 b m, .alu .and b y]) s fun s' => s'.gpr b = yv &&& m ∧ Keeps [b] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hy, Option.bind_some, isa,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [State.setReg, arithFlags, State.setFlags, ite_true, BitVec.and_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [State.setReg, arithFlags, State.setFlags, ite_eq_right hr]

theorem split_ok (y : Src) (s : State) {yv : BitVec 64}
    (hy : ∀ s', Keeps Bregs s s' → readSrc s' y = some yv) :
    WP isa (.block (split y)) s fun s' => Bs s' yv ∧ Keeps Bregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4)
    (fun j s' => Keeps Bregs s s' ∧ ∀ i < j, s'.gpr (B i) = yv &&& cls i)
    (fun j s' hj ⟨h₁, h₂⟩ => WP.mono (andCls_ok (B j) (cls j) y s' fun v => hy _ (h₁.setReg (B_mem j) v))
      fun s'' ⟨h₃, h₄⟩ => ⟨h₁.trans (h₄.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr ▸ B_mem j), fun i hi => ?_⟩)
    4 le_rfl s ⟨Keeps.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s' ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
  by_cases hij : i = j
  · rw [hij, h₃]
  · rw [h₄.1 _ fun h => hij (B_inj i (by omega) j hj (by simpa using h)), h₂ i (by omega)]

/-- The first `n` classes of the product, masked and added. -/
def prodPart (hv yv : BitVec 64) (n : Nat) : BitVec 128 :=
  (List.range n).foldl (fun r k => r ^^^ (classSum hv yv k 8 &&& (cls k ++ cls k))) 0

theorem prodPart_succ (hv yv : BitVec 64) (n : Nat) :
    prodPart hv yv (n + 1) = prodPart hv yv n ^^^ (classSum hv yv n 8 &&& (cls n ++ cls n)) := by
  simp only [prodPart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `product` computes `prodVal` of the table `q` and `y`. -/
theorem product_ok (y : Src) (q : Nat) {hv yv : BitVec 64} {s : State} (hT : Tbl s q hv)
    (hy : ∀ s', Keeps Bregs s s' → readSrc s' y = some yv) :
    WP isa (.block (product y q)) s fun s' =>
      s'.gpr PH ++ s'.gpr PL = prodVal hv yv ∧ Keeps prodClob s s' := by
  rw [product, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (split_ok y s hy) fun s₁ ⟨hB₁, hk₁⟩ => ?_
  refine WP.mono (zero_ok (by decide) s₁) fun s₂ ⟨hz, hk₂⟩ => ?_
  have hk : Keeps prodClob s s₂ := (hk₁.mono (by decide)).trans (hk₂.mono (by decide))
  have hT₂ := hT.keeps hk (by decide)
  have hB₂ := hB₁.keeps hk₂ fun j _ => by
    have := (B_not_mem (j := j))
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨this.2.1, this.2.2.1⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 4)
    (fun k s' => s'.gpr PH ++ s'.gpr PL = prodPart hv yv k ∧ Keeps clsClob s₂ s')
    (fun k s' _ ⟨h₁, h₂⟩ => WP.mono (clsCode_ok (hT₂.keeps h₂ (by decide))
      (hB₂.keeps h₂ fun j _ => by
        have := (B_not_mem (j := j))
        simp only [termClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
        exact ⟨this.1.1, this.1.2.1, this.1.2.2.1, this.1.2.2.2, this.2.1, this.2.2.1⟩))
      fun s'' ⟨h₃, h₄⟩ => ⟨by rw [h₃, h₁, prodPart_succ], h₂.trans h₄⟩)
    4 le_rfl s₂ ⟨hz, Keeps.refl _ _⟩) fun s₃ ⟨h₁, h₂⟩ => ⟨h₁, hk.trans (h₂.mono (by decide))⟩

end VG.Proof.Gcm.X86_64
