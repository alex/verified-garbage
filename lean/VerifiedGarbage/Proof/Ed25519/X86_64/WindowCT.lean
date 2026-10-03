import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqualCT
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the public inputs are the same in both runs). The digits are
read through pointers and a counter in the scratch, the same in both runs by
correctness; everything else is public by the taint analysis. The final
comparison branches on whether two points of the group are equal, which only
depends on the points represented.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off Keeps)
open VG.Impl.X25519.X86_64 (sc)

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : RelCT isa (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : RelCT isa (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  VG.RelCT.seq ((VG.RelCT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono
    (fun _ _ h => h) (fun _ _ h => h.2)) h₂

/-- Code the taint analysis proves constant time with `rdi` alone public. -/
theorem rdi_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .rdi = base)
    (h : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) c (fun _ _ => True)) :
    RelCT isa (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree_rdi {x y : State} (h : x.gpr .rdi = y.gpr .rdi) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-! ## Digits -/

/-- The digit's address: the pointer at byte `ptr` plus `add`, and the counter. -/
def digitPrefix (ptr add : Nat) : List Instr :=
  [.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (sc 56))]

theorem digitPrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {ptr add : Nat}
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P C : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P) (hc : s.mem.readW (off base 56) 64 = C) :
    WP isa (.block (digitPrefix ptr add)) s fun t =>
      t.gpr .rdi = base ∧ t.gpr .rsi = off P add ∧ t.gpr .rax = C := by
  rw [digitPrefix, show ([.mov .rsi (.mem (sc ptr)), .alu .add .rsi (.imm (BitVec.ofNat 32 add)),
      .mov .rax (.mem (sc 56))] : List Instr) =
    [.mov .rsi (.mem (sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      [.mov .rax (.mem (sc 56))]) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  have hb := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (loadPointer_ok hb .rax 56 (by decide)) fun c ⟨cp, kc⟩ => ?_
  refine ⟨(hb.of_keeps kc (by decide)).rdi, ?_, ?_⟩
  · rw [kc.1 _ (by decide), bp, ap, hp]
  · rw [cp, kb.2.1, ka.2.1, hc]

/-- A digit's code: its address by correctness, the rest by the taint analysis. -/
theorem digit_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {ptr add : Nat} {P : Addr}
    {rest : List Instr} (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31)
    (hP : ∀ x, WinCtx base kp sp A x → x.mem.readW (off base ptr) 64 = P)
    (hpre : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (digitPrefix ptr add))
      (fun _ _ => True))
    (hrest : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
      (.block rest) (fun _ _ => True)) :
    RelCT isa (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
      (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C))
      (.block (digitPrefix ptr add ++ rest)) (fun _ _ => True) := by
  have w (x : State) (h : WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) :=
    digitPrefix_ok h.1.scratch hptr hadd (hP x h.1) h.2
  refine blockAppend_ct ((VG.RelCT.wp (rdi_ct (fun x h => h.1.scratch.rdi) hpre)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.2.1.trans hy.2.1.symm, hx.2.2.trans hy.2.2.symm⟩

theorem agree_rsi_rax {x y : State} (h : x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rsi, .rax]) x y :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

theorem high_ct : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rsi, index := some .rax }, .shift .shr .rbx 4,
      .alu .test .rbx (.reg .rbx)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rsi, .rax]) (fun _ _ h => agree_rsi_rax h)
    (by fld_taint_decide)

theorem low_ct : RelCT isa (fun x y => x.gpr .rsi = y.gpr .rsi ∧ x.gpr .rax = y.gpr .rax)
    (.block [.movzx8 .rbx { base := .rsi, index := some .rax }, .alu .and .rbx (.imm 15)])
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rsi, .rax]) (fun _ _ h => agree_rsi_rax h)
    (by fld_taint_decide)

theorem prefixK_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (digitPrefix 7952 0))
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem prefixS_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block (digitPrefix 7944 32))
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

/-- What a digit's code reads, in both runs. -/
abbrev DigitCT (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) : Prop :=
  RelCT isa (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
    (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C)) (.block digit) (fun _ _ => True)

theorem digitKHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitHigh 7952 0) :=
  digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) prefixK_ct high_ct

theorem digitKLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitLow 7952 0) :=
  digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) prefixK_ct low_ct

theorem digitSHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitHigh 7944 32) :=
  digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) prefixS_ct high_ct

theorem digitSLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitLow 7944 32) :=
  digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) prefixS_ct low_ct

/-! ## Windows -/

theorem DigitSpec.of_keep {base : Addr} {s t : State} {digit : List Instr} {v : Nat}
    (h : DigitSpec base s digit v) (k : WinKeep base s t) : DigitSpec base t digit v :=
  fun u ku => h u (k.trans ku)

/-- A window's start, in one run: its digit is `v`, and the counter `C`. -/
structure WinPre (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  value : ∃ a, Rep (point (env s.mem base) 0 1 2 3) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem addDigitA_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ (pointAdd fld)))
    (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

theorem addDigitB_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
    (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ pointFromTableQ ++
      (pointAddCached fld))) (fun _ _ => True) := by
  apply taintFld (Taint.ofRegs [.rdi, .rbx]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2

/-- A digit and its addition: the branch is on the digit, the same in both runs. -/
theorem digitAdd_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit add : List Instr} {v o : Nat}
    (hdig : DigitCT base kp sp A C digit)
    (hadd : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi ∧ x.gpr .rbx = y.gpr .rbx)
      (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    RelCT isa (fun x y => WinPre base kp sp A C digit v x ∧ WinPre base kp sp A C digit v y)
      (.seq (.block digit) (addDigit o add)) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base kp sp A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .rdi = base ∧ u.gpr .rbx = BitVec.ofNat 64 v ∧ u.zf = some (decide (v = 0)) :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, uz, ku⟩ =>
      ⟨(ku.1 _ (by decide)).trans h.ctx.scratch.rdi, uv, uz⟩
  refine VG.RelCT.seq (VG.RelCT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩) ?_
  rw [addDigit]
  refine VG.RelCT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ _ => trivial)
  · simp only [eval, h.2.1.2.2, h.2.2.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.2.1.1.trans h.1.2.2.1.symm, h.1.2.1.2.1.trans h.1.2.2.2.1.symm⟩)
      (fun _ _ h => h)

theorem double4_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (double4 fld) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

instance : EdDouble (double4 fld) :=
  ⟨fun hs ha => WP.mono (double4_ok hs ha) fun _ ⟨r, h, k⟩ => ⟨r, h, WinKeep.of_double k⟩, double4_ct⟩

theorem windowA_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : DigitCT base kp sp A C digit) :
    RelCT isa (fun x y => WinPre base kp sp A C digit v x ∧ WinPre base kp sp A C digit v y)
      (windowA fld dbl digit) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base kp sp A C digit v x) :
      WP isa dbl x (WinPre base kp sp A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (EdDouble.ok h.ctx.scratch ha) fun b ⟨br, bh, kb⟩ => ?_
    exact ⟨h.ctx.of_keep kb, (bh 16 (by decide)).trans h.d, ⟨_, br⟩, kb.counter.trans h.counter,
      h.digit.of_keep kb, h.bound⟩
  rw [windowA]
  exact seq_same (rdi_ct (fun x h => h.ctx.scratch.rdi) (EdDouble.ct (dbl := dbl))) hw (digitAdd_ct hdig addDigitA_ct)

/-- After a window of `k` alone, the next digit's start. -/
theorem windowA_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit next : List Instr}
    {v w : Nat} {x : State}
    (h : WinPre base kp sp A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowA fld dbl digit) x (WinPre base kp sp A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (windowA_ok h.1.ctx h.1.d ha h.1.bound h.1.digit) fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb, bd, ⟨_, br⟩, kb.counter.trans h.1.counter, h.2.1.of_keep kb, h.2.2⟩

theorem windowAB_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digitA digitB : List Instr}
    {vA vB : Nat} (hA : DigitCT base kp sp A C digitA) (hB : DigitCT base kp sp A C digitB) :
    RelCT isa (fun x y => (WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (WinPre base kp sp A C digitA vA y ∧ DigitSpec base y digitB vB ∧ vB < 16))
      (windowAB fld dbl digitA digitB) (fun _ _ => True) := by
  rw [windowAB]
  exact seq_same ((windowA_ct hA).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => windowA_next h) (digitAdd_ct hB addDigitB_ct)

/-- After a window of both scalars, the next digits' start. -/
theorem windowAB_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr}
    {digitA digitB nextA nextB : List Instr} {vA vB wA wB : Nat} {x : State}
    (h : (WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (DigitSpec base x nextA wA ∧ wA < 16) ∧ (DigitSpec base x nextB wB ∧ wB < 16)) :
    WP isa (windowAB fld dbl digitA digitB) x fun u =>
      WinPre base kp sp A C nextA wA u ∧ DigitSpec base u nextB wB ∧ wB < 16 := by
  obtain ⟨a, ha⟩ := h.1.1.value
  refine WP.mono (windowAB_ok h.1.1.ctx h.1.1.d ha h.1.1.bound h.1.2.2 h.1.1.digit h.1.2.1)
    fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨⟨h.1.1.ctx.of_keep kb, bd, ⟨_, br⟩, kb.counter.trans h.1.1.counter, h.2.1.1.of_keep kb,
    h.2.1.2⟩, h.2.2.1.of_keep kb, h.2.2.2⟩

/-! ## Bytes -/

theorem batchBegin_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block batchBegin)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem batchTest_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi) (.block batchTest)
    (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem counterCmp_ct : RelCT isa (fun x y => x.gpr .rdi = y.gpr .rdi)
    (.block [.mov .rbx (.mem (sc 56)), .alu .cmp .rbx (.imm 32)]) (fun _ _ => True) :=
  taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => agree_rdi h) (by fld_taint_decide)

theorem nibble_lt (b : Nat) : b % 256 / 16 < 16 :=
  Nat.div_lt_of_lt_mul (by have := Nat.mod_lt b (show 256 > 0 by decide); omega)

/-- After `batchBegin`: the counter is `i`, and the scalars' bytes are those of `K` and `S`. -/
theorem byteBegin_ok {s₀ x : State} {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64)
    (h : WinLoop s₀ base kp sp A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base kp sp A a ∧ env a.mem base 16 = Spec.Ed25519.d ∧
      (∃ v, Rep (point (env a.mem base) 0 1 2 3) v) ∧
      a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      (a.mem (off kp i)).toNat = K / 256 ^ i % 256 ∧
      (i < 32 → (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256) := by
  refine WP.mono (batchBegin_ok h.ctx.scratch i h.counter) fun a ⟨_, av, ag, ar, aw, am⟩ => ?_
  have ka : ByteKeep base x a := ⟨fun r _ hb _ => ag r hb, ar, aw, am.mono (by decide) (by decide)⟩
  refine ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ⟨_, by rw [header_env am]; exact h.value⟩,
    av, ?_, fun hi32 => ?_⟩
  · rw [scalar_byte (n := 64) hi, ka.bytesK h.ctx, h.kVal]
  · rw [scalar_byte (n := 32) hi32, ka.bytesS h.ctx, h.sVal]

theorem byteStepA_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    RelCT isa (fun x y => (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) y)) (byteStepA fld dbl) (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let vH := K / 256 ^ i % 256 / 16
  let vL := K / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a => WinPre base kp sp A C (digitHigh 7952 0) vH a ∧
        DigitSpec base a (digitLow 7952 0) vL ∧ vL < 16 := by
    obtain ⟨s₀, h⟩ := h
    refine WP.mono (byteBegin_ok hi h) fun a ⟨actx, ad, av, ac, ak, _⟩ => ?_
    refine ⟨⟨actx, ad, av, ac, ?_, nibble_lt _⟩, ?_, Nat.mod_lt _ (by decide)⟩
    · rw [show vH = (a.mem (off kp i)).toNat / 16 by rw [ak]]; exact digitKHigh actx hi ac
    · rw [show vL = (a.mem (off kp i)).toNat % 16 by rw [ak]]; exact digitKLow actx hi ac
  have w3 (x : State) (h : WinPre base kp sp A C (digitLow 7952 0) vL x) :
      WP isa (windowA fld dbl (digitLow 7952 0)) x fun c => c.gpr .rdi = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (windowA_ok h.ctx h.d ha h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).rdi
  rw [byteStepA]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.rdi) batchBegin_ct)
    w1 ?_
  refine seq_same ((windowA_ct digitKHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => windowA_next h) ?_
  exact seq_same (windowA_ct digitKLow_ct) w3 (rdi_ct (fun _ h => h) counterCmp_ct)

theorem byteStepAB_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 32) :
    RelCT isa (fun x y => (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) y)) (byteStepAB fld dbl) (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let kH := K / 256 ^ i % 256 / 16
  let kL := K / 256 ^ i % 256 % 16
  let sH := S / 256 ^ i % 256 / 16
  let sL := S / 256 ^ i % 256 % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a =>
        (WinPre base kp sp A C (digitHigh 7952 0) kH a ∧ DigitSpec base a (digitHigh 7944 32) sH ∧
          sH < 16) ∧ (DigitSpec base a (digitLow 7952 0) kL ∧ kL < 16) ∧
          (DigitSpec base a (digitLow 7944 32) sL ∧ sL < 16) := by
    obtain ⟨s₀, h⟩ := h
    refine WP.mono (byteBegin_ok (by omega) h) fun a ⟨actx, ad, av, ac, ak, as⟩ => ?_
    have as := as hi
    refine ⟨⟨⟨actx, ad, av, ac, ?_, nibble_lt _⟩, ?_, nibble_lt _⟩, ⟨?_, Nat.mod_lt _ (by decide)⟩,
      ⟨?_, Nat.mod_lt _ (by decide)⟩⟩
    · rw [show kH = (a.mem (off kp i)).toNat / 16 by rw [ak]]; exact digitKHigh actx (by omega) ac
    · rw [show sH = (a.mem (off (off sp 32) i)).toNat / 16 by rw [as]]; exact digitSHigh actx hi ac
    · rw [show kL = (a.mem (off kp i)).toNat % 16 by rw [ak]]; exact digitKLow actx (by omega) ac
    · rw [show sL = (a.mem (off (off sp 32) i)).toNat % 16 by rw [as]]; exact digitSLow actx hi ac
  have w3 (x : State) (h : WinPre base kp sp A C (digitLow 7952 0) kL x ∧
      DigitSpec base x (digitLow 7944 32) sL ∧ sL < 16) :
      WP isa (windowAB fld dbl (digitLow 7952 0) (digitLow 7944 32)) x fun c => c.gpr .rdi = base := by
    obtain ⟨a, ha⟩ := h.1.value
    exact WP.mono (windowAB_ok h.1.ctx h.1.d ha h.1.bound h.2.2 h.1.digit h.2.1) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.1.ctx.scratch).rdi
  rw [byteStepAB]
  refine seq_same (rdi_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.rdi) batchBegin_ct)
    w1 ?_
  refine seq_same ((windowAB_ct digitKHigh_ct digitSHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)) (fun x h => windowAB_next h) ?_
  exact seq_same (windowAB_ct digitKLow_ct digitSLow_ct) w3 (rdi_ct (fun _ h => h) batchTest_ct)

/-! ## Loops -/

/-- A run of the loops: from a state satisfying `R₀`, with `c` bytes left. -/
def LoopRun (R₀ : State → Prop) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base kp sp A K S c x

theorem loopA_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    RelCT isa (fun x y => LoopRun R₀ base kp sp A K S 64 x ∧ LoopRun R₀ base kp sp A K S 64 y)
      (.loop (byteStepA fld dbl) .ne)
      (fun x y => LoopRun R₀ base kp sp A K S 32 x ∧ LoopRun R₀ base kp sp A K S 32 y) := by
  refine (VG.RelCT.loop (M := isa) (fun n x y => (LoopRun R₀ base kp sp A K S (32 + n) x ∧
    LoopRun R₀ base kp sp A K S (32 + n) y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : LoopRun R₀ base kp sp A K S (32 + (j + 1)) x) :
        WP isa (byteStepA fld dbl) x fun u => u.zf = some (decide (j = 0)) ∧
          LoopRun R₀ base kp sp A K S (32 + j) u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (VG.RelCT.wp ((byteStepA_ct (i := 32 + j) (by omega)).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    have ex : isa.eval .ne x = some (!decide (j = 0)) := by show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!decide (j = 0)) := by show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [ex, decide_eq_false hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [ex, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ h => hj (by omega)

theorem loopB_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    RelCT isa (fun x y => LoopRun R₀ base kp sp A K S 32 x ∧ LoopRun R₀ base kp sp A K S 32 y)
      (.loop (byteStepAB fld dbl) .ne)
      (fun x y => LoopRun R₀ base kp sp A K S 0 x ∧ LoopRun R₀ base kp sp A K S 0 y) := by
  refine (VG.RelCT.loop (M := isa) (fun n x y => (LoopRun R₀ base kp sp A K S n x ∧
    LoopRun R₀ base kp sp A K S n y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact VG.RelCT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : LoopRun R₀ base kp sp A K S (j + 1) x) :
        WP isa (byteStepAB fld dbl) x fun u => u.zf = some (decide (j = 0)) ∧ LoopRun R₀ base kp sp A K S j u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (VG.RelCT.wp ((byteStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    have ex : isa.eval .ne x = some (!decide (j = 0)) := by show eval .ne x = _; simp only [eval, xz, Option.map_some]
    have ey : isa.eval .ne y = some (!decide (j = 0)) := by show eval .ne y = _; simp only [eval, yz, Option.map_some]
    refine ⟨ex.trans ey.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [ex, decide_eq_false hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [ex, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact VG.RelCT.of_false fun _ _ h => hj (by omega)

/-! ## The comparison -/

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scratch s base ∧ Rep (point (env s.mem base) 0 1 2 3) P ∧ Rep (point (env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (Impl.Ed25519.X86_64.pointEqual fld) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) s fun t =>
        Scratch t base ∧ t.zf = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨h.1.of_keep kt, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (rep_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact rep_cross_y h.2.1 h.2.2
  have hp := VG.RelCT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : RelCT isa (fun s t => (Scratch s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scratch t base ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual fld 10 11)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    exact fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi
  have hw2 (s : State) (h : Scratch s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual fld 10 11)) s fun t => t.zf = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun _ k => by
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := VG.RelCT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.X86_64.pointEqual]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine VG.RelCT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
    · exact fun _ _ h => by simp only [eval, h.2.1, h.2.2]
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86_64
