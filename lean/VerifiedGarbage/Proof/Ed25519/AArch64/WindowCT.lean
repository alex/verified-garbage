import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqualCT
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport

/-!
# Verification's windows: what their traces depend on

Untrusted. The windows branch on the digits of the scalars and address the
tables by them, so their traces depend on the scalars: both runs must use
the same ones (in verification, the public inputs are the same in both
runs). The digits are read through pointers and a counter in the scratch,
the same in both runs by correctness; everything else is public by the
taint analysis. The skipped bytes of `k` are its leading zeros, the same in
both runs. The final comparison branches on whether two points of the group
are equal, which only depends on the points represented.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : CT (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : CT (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  CT.seq ((CT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) h₂

theorem agree_x0 {x y : State} (h : x.gpr .x0 = y.gpr .x0) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [.x0], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-- Code the taint analysis proves constant time with `x0` alone public. -/
theorem x0_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .x0 = base)
    (h : CT (fun x y => x.gpr .x0 = y.gpr .x0) c (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree2 {x y : State} {a b : Reg} (h : x.gpr a = y.gpr a ∧ x.gpr b = y.gpr b) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [a, b], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

/-! ## Digits -/

/-- The digit's pointer and counter. -/
def digitPrefix (ptr : Nat) : List Instr := [ld .x2 ptr, ld .x8 56]

theorem digitPrefix_ok {s : State} {base : Addr} (hs : Scr s base) {ptr : Nat}
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) {P C : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P) (hc : s.mem.readW (off base 56) 64 = C) :
    WP isa (.block (digitPrefix ptr)) s fun t => t.gpr .x2 = P ∧ t.gpr .x8 = C := by
  rw [digitPrefix, show ([ld .x2 ptr, ld .x8 56] : List Instr) = [ld .x2 ptr] ++ [ld .x8 56] from rfl,
    WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 ptr hpa hptr) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (loadPointer_ok (hs.of_keeps ka (by decide)) .x8 56 (by decide) (by decide))
    fun t ⟨tp, kt⟩ => ?_
  exact ⟨by rw [kt.gpr _ (by decide), ap, hp], by rw [tp, ka.mem, hc]⟩

/-- A digit's code: its address by correctness, the rest by the taint analysis. -/
theorem digit_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {ptr : Nat} {P : Addr}
    {rest : List Instr} (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192)
    (hP : ∀ x, WinCtx base kp sp A x → x.mem.readW (off base ptr) 64 = P)
    (hpre : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block (digitPrefix ptr)) (fun _ _ => True))
    (hrest : CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
      (.block rest) (fun _ _ => True)) :
    CT (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
      (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C))
      (.block (digitPrefix ptr ++ rest)) (fun _ _ => True) := by
  have w (x : State) (h : WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) :=
    digitPrefix_ok h.1.scratch hpa hptr (hP x h.1) h.2
  refine blockAppend_ct ((CT.wp (x0_ct (fun x h => h.1.scratch.x0) hpre)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

theorem prefix_ct (ptr : Nat) (hptr : ptr = 7952 ∨ ptr = 7944) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block (digitPrefix ptr)) (fun _ _ => True) := by
  rcases hptr with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem high_ct (add : Nat) (hadd : add = 0 ∨ add = 32) :
    CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x2 .x8, .ldrb .x19 .x8 add, .lsr .x .x19 .x19 4]) (fun _ _ => True) := by
  rcases hadd with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x2, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

theorem low_ct (add : Nat) (hadd : add = 0 ∨ add = 32) :
    CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x2 .x8, .ldrb .x19 .x8 add, .lsl .x .x19 .x19 60, .lsr .x .x19 .x19 60])
      (fun _ _ => True) := by
  rcases hadd with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x2, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

/-- What a digit's code reads, in both runs. -/
abbrev DigitCT (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) : Prop :=
  CT (fun x y => (WinCtx base kp sp A x ∧ x.mem.readW (off base 56) 64 = C) ∧
    (WinCtx base kp sp A y ∧ y.mem.readW (off base 56) 64 = C)) (.block digit) (fun _ _ => True)

theorem digitKHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitHigh 7952 0) :=
  digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) (prefix_ct _ (.inl rfl))
    (high_ct 0 (.inl rfl))

theorem digitKLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitLow 7952 0) :=
  digit_ct (P := kp) (by decide) (by decide) (fun _ h => h.kHeader) (prefix_ct _ (.inl rfl))
    (low_ct 0 (.inl rfl))

theorem digitSHigh_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitHigh 7944 32) :=
  digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) (prefix_ct _ (.inr rfl))
    (high_ct 32 (.inr rfl))

theorem digitSLow_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} :
    DigitCT base kp sp A C (digitLow 7944 32) :=
  digit_ct (P := sp) (by decide) (by decide) (fun _ h => h.sHeader) (prefix_ct _ (.inr rfl))
    (low_ct 32 (.inr rfl))

/-! ## Windows -/

/-- A window's start, in one run: its digit is `v`, and the counter `C`. -/
structure WinPre (base kp sp : Addr) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  value : ∃ a, RepP (point (env s.mem base) 0 1 2 3) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem addDigit_ct (o : Nat) (add : List Instr) (h : o = 5376 ∧ add = pointAddCachedP ∨
    o = 5376 ∧ add = pointAddCached ∨ o = 2048 ∧ add = pointAddCachedP) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)

/-- A digit and its addition: the branch is on the digit, the same in both runs. -/
theorem digitAdd_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit add : List Instr} {v o : Nat}
    (hdig : DigitCT base kp sp A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => WinPre base kp sp A C digit v x ∧ WinPre base kp sp A C digit v y)
      (.seq (.block digit) (addDigit o add)) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base kp sp A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .x0 = base ∧ u.gpr .x19 = BitVec.ofNat 64 v :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, ku⟩ =>
      ⟨(ku.gpr _ (by decide)).trans h.ctx.scratch.x0, uv⟩
  refine CT.seq ((CT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  rw [addDigit]
  refine CT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ h => ⟨h.1, trivial⟩)
  · simp only [eval, read_x, h.1.2, h.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.trans h.1.2.2.symm⟩)
      (fun _ _ h => h)

theorem doubleWindow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) doubleWindow (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem windowWith_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit add : List Instr}
    {v : Nat} (hdig : DigitCT base kp sp A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => WinPre base kp sp A C digit v x ∧ WinPre base kp sp A C digit v y)
      (windowWith digit add) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base kp sp A C digit v x) :
      WP isa doubleWindow x (WinPre base kp sp A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (doubleWindow_ok h.ctx.scratch ha) fun b ⟨br, bh, bk⟩ => ?_
    have kb := WinKeep.of_double bk
    exact ⟨h.ctx.of_keep kb, (bh 16 (by decide)).trans h.d, ⟨_, br.proj⟩, kb.counter.trans h.counter,
      h.digit.of_keep kb, h.bound⟩
  rw [windowWith]
  exact seq_same (x0_ct (fun x h => h.ctx.scratch.x0) doubleWindow_ct) hw (digitAdd_ct hdig hadd)

theorem windowA_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : DigitCT base kp sp A C digit) :
    CT (fun x y => WinPre base kp sp A C digit v x ∧ WinPre base kp sp A C digit v y)
      (windowA digit) (fun _ _ => True) :=
  windowWith_ct hdig (addDigit_ct _ _ (.inl ⟨rfl, rfl⟩))

/-- After a window of `k`, the next digit's start. -/
theorem windowWith_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit next add : List Instr}
    {full : Bool} (hadd : AddSpec add cache full) {v w : Nat} {x : State}
    (h : WinPre base kp sp A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowWith digit add) x (WinPre base kp sp A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (windowWith_ok h.1.ctx h.1.d ha hadd h.1.bound h.1.digit) fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb, bd, ⟨_, br.proj⟩, kb.counter.trans h.1.counter, h.2.1.of_keep kb, h.2.2⟩

theorem windowA_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digit next : List Instr}
    {v w : Nat} {x : State}
    (h : WinPre base kp sp A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowA digit) x (WinPre base kp sp A C next w) :=
  windowWith_next pointAddCachedP_spec h

theorem windowAB_ct {base kp sp : Addr} {A : EPoint dZ} {C : Addr} {digitA digitB : List Instr}
    {vA vB : Nat} (hA : DigitCT base kp sp A C digitA) (hB : DigitCT base kp sp A C digitB) :
    CT (fun x y => (WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (WinPre base kp sp A C digitA vA y ∧ DigitSpec base y digitB vB ∧ vB < 16))
      (windowAB digitA digitB) (fun _ _ => True) := by
  rw [windowAB]
  exact seq_same ((windowWith_ct hA (addDigit_ct _ _ (.inr (.inl ⟨rfl, rfl⟩)))).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => windowWith_next pointAddCached_spec h)
    (digitAdd_ct hB (addDigit_ct _ _ (.inr (.inr ⟨rfl, rfl⟩))))

/-- After a window of both scalars, the next digits' start. -/
theorem windowAB_next {base kp sp : Addr} {A : EPoint dZ} {C : Addr}
    {digitA digitB nextA nextB : List Instr} {vA vB wA wB : Nat} {x : State}
    (h : (WinPre base kp sp A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (DigitSpec base x nextA wA ∧ wA < 16) ∧ (DigitSpec base x nextB wB ∧ wB < 16)) :
    WP isa (windowAB digitA digitB) x fun u =>
      WinPre base kp sp A C nextA wA u ∧ DigitSpec base u nextB wB ∧ wB < 16 := by
  obtain ⟨a, ha⟩ := h.1.1.value
  refine WP.mono (windowAB_ok h.1.1.ctx h.1.1.d ha h.1.1.bound h.1.2.2 h.1.1.digit h.1.2.1)
    fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨⟨h.1.1.ctx.of_keep kb, bd, ⟨_, br⟩, kb.counter.trans h.1.1.counter, h.2.1.1.of_keep kb,
    h.2.1.2⟩, h.2.2.1.of_keep kb, h.2.2.2⟩

/-! ## Bytes -/

theorem batchBegin_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchBegin) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem batchTest_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchTest) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem aboveLow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block aboveLow) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem nibble_lt (b : Nat) : b % 256 / 16 < 16 :=
  Nat.div_lt_of_lt_mul (by have := Nat.mod_lt b (show 256 > 0 by decide); omega)

/-- After `batchBegin`: the counter is `i`, and the scalars' bytes are those of `K` and `S`. -/
theorem byteBegin_ok {s₀ x : State} {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64)
    (h : WinLoop s₀ base kp sp A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base kp sp A a ∧ env a.mem base 16 = Spec.Ed25519.d ∧
      (∃ v, RepP (point (env a.mem base) 0 1 2 3) v) ∧
      a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i ∧
      (a.mem (off kp i)).toNat = K / 256 ^ i % 256 ∧
      (i < 32 → (a.mem (off (off sp 32) i)).toNat = S / 256 ^ i % 256) := by
  refine WP.mono (batchBegin_ok h.ctx.scratch i h.counter) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_
  have ka : ByteKeep base x a := ByteKeep.of_counter ag ar aw asp am
  refine ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ⟨_, by rw [header_env am]; exact h.value⟩,
    av, ?_, fun hi32 => ?_⟩
  · rw [scalar_byte (n := 64) hi, ka.bytesK h.ctx, h.kVal]
  · rw [scalar_byte (n := 32) hi32, ka.bytesS h.ctx, h.sVal]

theorem byteStepA_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) y)) byteStepA (fun _ _ => True) := by
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
      WP isa (windowA (digitLow 7952 0)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (windowA_ok h.ctx h.d ha h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).x0
  rw [byteStepA]
  refine seq_same (x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) batchBegin_ct)
    w1 ?_
  refine seq_same ((windowA_ct digitKHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => windowA_next h) ?_
  exact seq_same (windowA_ct digitKLow_ct) w3 (x0_ct (fun _ h => h) aboveLow_ct)

theorem byteStepAB_ct {base kp sp : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 32) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base kp sp A K S (i + 1) y)) byteStepAB (fun _ _ => True) := by
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
      WP isa (windowAB (digitLow 7952 0) (digitLow 7944 32)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.1.value
    exact WP.mono (windowAB_ok h.1.ctx h.1.d ha h.1.bound h.2.2 h.1.digit h.2.1) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.1.ctx.scratch).x0
  rw [byteStepAB]
  refine seq_same (x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) batchBegin_ct)
    w1 ?_
  refine seq_same ((windowAB_ct digitKHigh_ct digitSHigh_ct).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)) (fun x h => windowAB_next h) ?_
  exact seq_same (windowAB_ct digitKLow_ct digitSLow_ct) w3 (x0_ct (fun _ h => h) batchTest_ct)

/-! ## Loops -/

/-- A run of the loops: from a state satisfying `R₀`, with `c` bytes left. -/
def LoopRun (R₀ : State → Prop) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base kp sp A K S c x

theorem loopA_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 32) :
    CT (fun x y => LoopRun R₀ base kp sp A K S (32 + n) x ∧ LoopRun R₀ base kp sp A K S (32 + n) y)
      (.loop byteStepA (.nonzero .x .x19))
      (fun x y => LoopRun R₀ base kp sp A K S 32 x ∧ LoopRun R₀ base kp sp A K S 32 y) := by
  refine (CT.loop (fun n x y => (LoopRun R₀ base kp sp A K S (32 + n) x ∧
    LoopRun R₀ base kp sp A K S (32 + n) y) ∧ 0 < n ∧ n ≤ 32) ?_ n).mono
      (fun _ _ h => ⟨h, hn0, hn⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : LoopRun R₀ base kp sp A K S (32 + (j + 1)) x) :
        WP isa byteStepA x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          LoopRun R₀ base kp sp A K S (32 + j) u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((byteStepA_ct (i := 32 + j) (by omega)).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

theorem windowsA_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc32 : 32 ≤ c) (hc64 : c ≤ 64) :
    CT (fun x y => LoopRun R₀ base kp sp A K S c x ∧ LoopRun R₀ base kp sp A K S c y) windowsA
      (fun x y => LoopRun R₀ base kp sp A K S 32 x ∧ LoopRun R₀ base kp sp A K S 32 y) := by
  have hw (x : State) (h : LoopRun R₀ base kp sp A K S c x) : WP isa (.block aboveLow) x fun u =>
      eval (.nonzero .x .x19) u = some (decide (c ≠ 32)) ∧ LoopRun R₀ base kp sp A K S c u := by
    obtain ⟨s₀, r₀, h⟩ := h
    exact WP.mono (aboveLow_ok h.ctx.scratch c hc64 h.counter) fun u ⟨uz, ku⟩ =>
      ⟨uz, s₀, r₀, h.of_keeps ku (by decide)⟩
  rw [windowsA]
  refine CT.seq ((CT.wp (x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0)
    aboveLow_ct) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => h.1.1.trans h.2.1.symm) ?_ ?_
  · obtain ⟨n, rfl⟩ : ∃ n, c = 32 + n := ⟨c - 32, by omega⟩
    by_cases hn : n = 0
    · subst hn
      exact CT.of_false fun x y h => by
        have := h.2; rw [h.1.1.1] at this; cases this
    · exact (loopA_ct n (by omega) (by omega)).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩)
        (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y h => ⟨h.1, ?_⟩
    have hc : c = 32 := by
      by_contra hne
      have := h.2.2; rw [h.2.1.1.1, decide_eq_true hne] at this; cases this
    subst hc
    exact ⟨h.2.1.1.2, h.2.1.2.2⟩

theorem loopB_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => LoopRun R₀ base kp sp A K S 32 x ∧ LoopRun R₀ base kp sp A K S 32 y)
      (.loop byteStepAB (.nonzero .x .x19))
      (fun x y => LoopRun R₀ base kp sp A K S 0 x ∧ LoopRun R₀ base kp sp A K S 0 y) := by
  refine (CT.loop (fun n x y => (LoopRun R₀ base kp sp A K S n x ∧
    LoopRun R₀ base kp sp A K S n y) ∧ 0 < n ∧ n ≤ 32) ?_ 32).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 32
  · have hw (x : State) (h : LoopRun R₀ base kp sp A K S (j + 1) x) :
        WP isa byteStepAB x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          LoopRun R₀ base kp sp A K S j u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((byteStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

/-! ## Skipping the leading zero bytes of `k` -/

/-- A run of the skipping: from a state satisfying `R₀`, with `32 + n` bytes left. -/
def SkipRun (R₀ : State → Prop) (base kp sp : Addr) (A : EPoint dZ) (K S n : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipInv s₀ base kp sp A K S n x

/-- The byte's pointer and the counter, less one. -/
def skipPrefix : List Instr := [ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952]

theorem skipPrefix_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block skipPrefix) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem skipRest_ct : CT (fun x y => x.gpr .x2 = y.gpr .x2 ∧ x.gpr .x8 = y.gpr .x8)
    (.block [.add .x .x2 .x2 .x8, .ldrb .x19 .x2 0]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x2, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

theorem skipPrefix_ok {s : State} {base kp : Addr} (hs : Scr s base)
    (hp : s.mem.readW (off base 7952) 64 = kp) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipPrefix) s fun t => t.gpr .x2 = kp ∧ t.gpr .x8 = BitVec.ofNat 64 j := by
  rw [skipPrefix, show ([ld .x8 56, .subImm .x .x8 .x8 1, ld .x2 7952] : List Instr) =
    [ld .x8 56] ++ ([.subImm .x .x8 .x8 1] ++ [ld .x2 7952]) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun b ⟨bv, kb⟩ => ?_
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .x2 7952
    (by decide) (by decide)) fun t ⟨tp, kt⟩ => ?_
  exact ⟨by rw [tp, kb.mem, ka.mem, hp], by rw [kt.gpr _ (by decide), bv]⟩

theorem movzZero_ct : CT (fun _ _ => True) (.block [.movz .w .x19 0 0]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs []) (fun _ _ _ => agree_ofRegs (by simp)) (by taint_decide)

theorem skipStore_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0)
    (.block [st .x8 56, .subImm .x .x19 .x8 32]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem skipBody_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} :
    CT (fun x y => SkipRun R₀ base kp sp A K S (j + 1) x ∧ SkipRun R₀ base kp sp A K S (j + 1) y)
      skipBody (fun _ _ => True) := by
  let P := SkipRun R₀ base kp sp A K S (j + 1)
  have hx0 (x : State) (h : P x) : x.gpr .x0 = base := by
    obtain ⟨_, _, h, _⟩ := h; exact h.ctx.scratch.x0
  have hpre (x : State) (h : P x) : WP isa (.block skipPrefix) x fun t =>
      t.gpr .x2 = kp ∧ t.gpr .x8 = BitVec.ofNat 64 (32 + j) := by
    obtain ⟨_, _, h, _⟩ := h
    exact skipPrefix_ok h.ctx.scratch h.ctx.kHeader (32 + j) (by rw [h.counter]; rfl)
  have hload : CT (fun x y => P x ∧ P y) (.block skipLoad) (fun _ _ => True) := by
    rw [show skipLoad = skipPrefix ++ [.add .x .x2 .x2 .x8, .ldrb .x19 .x2 0] from rfl]
    refine blockAppend_ct ((CT.wp (x0_ct hx0 skipPrefix_ct) fun x y h => ⟨hpre x h.1, hpre y h.2⟩).mono
      (fun _ _ h => h) ?_) skipRest_ct
    intro x y ⟨_, hx, hy⟩
    exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩
  have hw (x : State) (h : P x) : WP isa (.block skipLoad) x fun u => u.gpr .x0 = base ∧
      u.gpr .x19 = BitVec.ofNat 64 (K / 256 ^ (32 + j) % 256) := by
    obtain ⟨_, _, hl, _, _, hn⟩ := h
    refine WP.mono (skipLoad_ok hl.ctx.scratch hl.ctx.kHeader (32 + j) (by rw [hl.counter]; rfl)
      (hl.ctx.kRead _ (by omega))) fun u ⟨_, uv, ku⟩ => ⟨(ku.gpr _ (by decide)).trans
        hl.ctx.scratch.x0, by rw [uv, scalar_byte (n := 64) (by omega), hl.kVal]⟩
  rw [skipBody]
  refine CT.seq ((CT.wp hload fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => by simp only [eval, read_x, h.1.2, h.2.2]) ?_ ?_
  · exact movzZero_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact skipStore_ct.mono (fun _ _ h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

theorem skipZero_ct {R₀ : State → Prop} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => SkipRun R₀ base kp sp A K S 32 x ∧ SkipRun R₀ base kp sp A K S 32 y) skipZero
      (fun x y => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ LoopRun R₀ base kp sp A K S c x ∧
        LoopRun R₀ base kp sp A K S c y) := by
  rw [skipZero]
  refine CT.loop (fun n x y => SkipRun R₀ base kp sp A K S n x ∧ SkipRun R₀ base kp sp A K S n y)
    ?_ 32
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, h, _⟩ := h.1; exact Nat.lt_irrefl 0 h
  by_cases hj : j < 32
  · have hw (x : State) (h : SkipRun R₀ base kp sp A K S (j + 1) x) : WP isa skipBody x fun u =>
        eval (.nonzero .x .x19) u = some (skipOn K j) ∧
        (skipOn K j = false → LoopRun R₀ base kp sp A K S (skipEnd K j) u) ∧
        (skipOn K j = true → SkipRun R₀ base kp sp A K S j u) := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (skipBody_ok h) fun u ⟨uz, uf, ut⟩ =>
        ⟨uz, fun hf => ⟨s₀, r₀, uf hf⟩, fun ht => ⟨s₀, r₀, ut ht⟩⟩
    refine (CT.wp skipBody_ct fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have hs : skipOn K j = false := Option.some.inj (xz.symm.trans he)
      exact ⟨skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2, xf hs, yf hs⟩
    · have hs : skipOn K j = true := Option.some.inj (xz.symm.trans he)
      exact ⟨j, by omega, xt hs, yt hs⟩
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, _, h⟩ := h.1; exact hj (by omega)

/-! ## The comparison -/

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scr s base ∧ RepP (point (env s.mem base) 0 1 2 3) P ∧ RepP (point (env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    CT (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact repP_cross_y h.2.1 h.2.2
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : CT (fun s t => (Scr s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scr t base ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual 10 11)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw2 (s : State) (h : Scr s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun t k => by
      change some (t.gpr .x8 == 0) = _
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := CT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine CT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (CT.ite ?_ ?_ ?_)
    · exact fun _ _ h => h.2.1.trans h.2.2.symm
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
