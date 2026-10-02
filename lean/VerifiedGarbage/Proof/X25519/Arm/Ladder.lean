import VerifiedGarbage.Proof.X25519.Arm.Slots
import VerifiedGarbage.Proof.X25519.Ladder

/-!
# X25519 on 32-bit ARM: the ladder

One iteration of the ladder (`step_ok`) takes the elements `x1, x2, z2, x3,
z3, a24` from the state after the bits `254` down to `n` (`ladderAfter k x1
n`) to the state after `n - 1`, with the swap in `r10` and the counter in
`r11`; the loop (`ladder_ok`) runs it for the bits 254 down to 0.
-/

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe Ladder ladderStep cswap a24)
open VG.Proof.X25519 (toFe ladderAfter ladderAfter_step ladderStep_eq bit bit_le ladderAfter_swap_le)

/-- `s'` is `s` but for the registers `r1`–`r11`, the flags and the field
area. -/
structure Stp (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s'
  frame : Frame [FA ACC b] s.mem s'.mem

theorem Stp.refl (b : BitVec 32) (s : State) : Stp b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Stp.trans {b : BitVec 32} {s₁ s₂ s₃ : State} (h₁ : Stp b s₁ s₂) (h₂ : Stp b s₂ s₃) : Stp b s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.frame.trans h₂.frame⟩

theorem Stp.of_rest {b : BitVec 32} {s s' : State} {ws : List Reg} (hr : Rest ws s s')
    (hws : ∀ r ∈ ws, r ∈ [Reg.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11])
    (hm : s'.mem = s.mem) : Stp b s s' := ⟨hr.mono hws, by rw [hm]; exact Frame.refl _ _⟩

/-- Between field operations, from `s0`: `r10` and `r11` hold `a` and `c`,
and the slots `qs` the elements `v`. -/
structure Cur (b : BitVec 32) (s0 : State) (a c : BitVec 32) (qs : List Nat) (v : Nat → Fe) (s : State) :
    Prop where
  ctx : Ctx b s
  stp : Stp b s0 s
  r10 : s.gpr .r10 = a
  r11 : s.gpr .r11 = c
  slots : SlotsOk s.mem (State.addr b) qs v

section
variable {b : BitVec 32} {s0 : State} {a c : BitVec 32} {qs : List Nat} {v : Nat → Fe}

theorem Cur.next {s s' : State} (h : Cur b s0 a c qs v s) (hr : Rest clob s s')
    (hf : Frame [FA ACC b] s.mem s'.mem) {qs' : List Nat} {v' : Nat → Fe}
    (hS : SlotsOk s'.mem (State.addr b) qs' v') : Cur b s0 a c qs' v' s' :=
  ⟨h.ctx.of_rest hr (by decide), h.stp.trans ⟨hr.mono (by decide), hf⟩,
    by rw [hr.gpr _ (by decide), h.r10], by rw [hr.gpr _ (by decide), h.r11], hS⟩

theorem opMul {o x y : Nat} (hq : Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (mul o x y) s (Cur b s0 a c (o :: qs) (upd v o (v x * v y))) :=
  WP.mono (mulS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opAdd {o x y : Nat} (hq : Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (add o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x + v y))) :=
  WP.mono (addS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

theorem opSub {o x y : Nat} (hq : Sep1 ACC o qs = true) (ho : 64 ≤ o ∧ o + 64 ≤ ACC) (hx : x ∈ qs)
    (hy : y ∈ qs) {s : State} (h : Cur b s0 a c qs v s) :
    WP isa (.block (sub o x y)) s (Cur b s0 a c (o :: qs) (upd v o (v x - v y))) :=
  WP.mono (subS (by decide) hq ho hx hy h.ctx h.slots) fun _ ⟨hr, hf, hS⟩ => h.next hr hf hS

end

/-! ## Sequences of field operations -/

/-- A field operation: `o = x · y`, `x + y` or `x - y`. -/
inductive FOp
  | mul (o x y : Nat)
  | add (o x y : Nat)
  | sub (o x y : Nat)

def FOp.code : FOp → Prog isa
  | .mul o x y => Impl.X25519.Arm.mul o x y
  | .add o x y => .block (Impl.X25519.Arm.add o x y)
  | .sub o x y => .block (Impl.X25519.Arm.sub o x y)

def FOp.out : FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ => o

def FOp.x : FOp → Nat
  | .mul _ x _ | .add _ x _ | .sub _ x _ => x

def FOp.y : FOp → Nat
  | .mul _ _ y | .add _ _ y | .sub _ _ y => y

def FOp.val : FOp → (Nat → Fe) → Fe
  | .mul _ x y, v => v x * v y
  | .add _ x y, v => v x + v y
  | .sub _ x y, v => v x - v y

/-- The operations `ops`, then `k`. -/
def opsCode : List FOp → Prog isa → Prog isa
  | [], k => k
  | op :: ops, k => .seq op.code (opsCode ops k)

/-- Each operation's slots are separate or equal, below `ACC`, and its inputs
known. -/
def opsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, qs => Sep1 ACC op.out qs && 64 ≤ op.out && op.out + 64 ≤ ACC && qs.contains op.x &&
      qs.contains op.y && opsOk ops (op.out :: qs)

/-- The elements after the operations. -/
def runOps : List FOp → (Nat → Fe) → Nat → Fe
  | [], v => v
  | op :: ops, v => runOps ops (upd v op.out (op.val v))

/-- The slots known after the operations. -/
def outsQ : List FOp → List Nat → List Nat
  | [], qs => qs
  | op :: ops, qs => outsQ ops (op.out :: qs)

theorem op_ok {b : BitVec 32} {s0 : State} {a c : BitVec 32} {qs : List Nat} {v : Nat → Fe} (op : FOp)
    (hq : Sep1 ACC op.out qs = true) (ho : 64 ≤ op.out ∧ op.out + 64 ≤ ACC) (hx : op.x ∈ qs) (hy : op.y ∈ qs)
    {s : State} (h : Cur b s0 a c qs v s) :
    WP isa op.code s (Cur b s0 a c (op.out :: qs) (upd v op.out (op.val v))) := by
  cases op with
  | mul o x y => exact opMul hq ho hx hy h
  | add o x y => exact opAdd hq ho hx hy h
  | sub o x y => exact opSub hq ho hx hy h

theorem ops_ok {b : BitVec 32} {s0 : State} {a c : BitVec 32} {k : Prog isa} {Q : State → Prop} :
    ∀ (ops : List FOp) (qs : List Nat) (v : Nat → Fe) (s : State), opsOk ops qs = true →
      Cur b s0 a c qs v s → (∀ s', Cur b s0 a c (outsQ ops qs) (runOps ops v) s' → WP isa k s' Q) →
      WP isa (opsCode ops k) s Q
  | [], _, _, s, _, h, hk => hk s h
  | op :: ops, qs, v, s, hok, h, hk => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
    exact WP.seq (WP.mono (op_ok op h1 ⟨h2, h3⟩ h4 h5 h) fun s' h' => ops_ok ops _ _ s' h6 h' hk)

/-! ## One iteration -/

/-- The field operations of an iteration, after the swaps. -/
def ladOps : List FOp :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB, .add C X3 Z3, .sub D X3 Z3,
    .mul DA D A, .mul CB C B, .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3,
    .mul Z3 X1 Z3, .mul X2 AA BB, .mul Z2 A24 E, .add Z2 AA Z2, .mul Z2 E Z2]

/-- The slots the ladder's state lives in. -/
def LQ : List Nat := [X1, X2, Z2, X3, Z3, A24]

theorem ladOps_ok : opsOk ladOps LQ = true := by decide

/-- The elements of the ladder's state `st`, and `x1` and `a24`. -/
def ladV (x1 : Fe) (st : Ladder) (q : Nat) : Fe :=
  if q = X1 then x1 else if q = X2 then st.x2 else if q = Z2 then st.z2 else if q = X3 then st.x3
  else if q = Z3 then st.z3 else a24

theorem cswap_fst (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).1 = sel sw x y := by
  unfold Spec.X25519.cswap sel; split <;> rfl

theorem cswap_snd (sw : Nat) (x y : Fe) : (Spec.X25519.cswap sw x y).2 = sel sw y x := by
  unfold Spec.X25519.cswap sel; split <;> rfl

/-- The elements after an iteration. -/
theorem ladOps_vals (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ∀ q ∈ LQ, runOps ladOps (swapV Z2 Z3 (st.swap ^^^ bit k t) (swapV X2 X3 (st.swap ^^^ bit k t)
      (ladV x1 st))) q = ladV x1 (ladderStep k x1 st t) q := by
  intro q hq
  rw [ladderStep_eq]
  simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ladOps, runOps, FOp.out, FOp.val, upd, swapV, ladV, cswap_fst, cswap_snd, X1, X2, Z2, X3,
      Z3, A, B, C, D, AA, BB, E, DA, CB, A24, Nat.reduceEqDiff, ite_true, ite_false]

theorem ofNat_xor {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    BitVec.ofNat 32 x ^^^ BitVec.ofNat 32 y = BitVec.ofNat 32 (x ^^^ y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_imm hx, toNat_imm hy, toNat_imm (Nat.xor_lt_two_pow hx hy)]

theorem xor_le_one {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

theorem ea2 {b : BitVec 32} (hfit : b.toNat + 4096 ≤ 2 ^ 32) {x d : Nat} (h : x + d < 4096) :
    State.addr (b + BitVec.ofNat 32 x + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 (x + d) := by
  rw [Offset.add_add]; exact addr_add (by omega)

/-- The loop invariant of the ladder from `sL`, before the iteration for the
bit `n - 1`. -/
structure LadInv (b : BitVec 32) (k : Nat) (x1 : Fe) (sL : State) (n : Nat) (s : State) : Prop where
  cur : Cur b sL (BitVec.ofNat 32 (ladderAfter k x1 n).swap) (BitVec.ofNat 32 n) LQ
    (ladV x1 (ladderAfter k x1 n)) s

/-- The bits of the scalar in `BITS`. -/
def Bits (b : BitVec 32) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 255, m (State.addr b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (bit k t)

theorem head_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa (.block stepHead) s (Cur b sL (BitVec.ofNat 32 (bit k (n - 1))) (BitVec.ofNat 32 (n - 1)) LQ
      (swapV Z2 Z3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1))
        (swapV X2 X3 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) (ladV x1 (ladderAfter k x1 n))))) := by
  obtain ⟨hcur⟩ := h
  have hc := hcur.ctx
  have hfit := hc.fit
  have hB : BITS = 1280 := rfl
  have hsw := ladderAfter_swap_le k x1 hn'
  have hbt := bit_le k (n - 1)
  have hx := xor_le_one hsw hbt
  simp only [stepHead, mask, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  have e11 : s1.gpr .r11 = BitVec.ofNat 32 (n - 1) := by
    rw [u1.gpr]; show s.gpr .r11 - 1 = _
    rw [hcur.r11]
    apply BitVec.eq_of_toNat_eq
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega), t1]
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  refine wp_ldrb (a := State.addr b + BitVec.ofNat 64 (n - 1 + BITS)) (by decide)
    (by rw [u2.gpr]; show State.addr (s1.gpr .r0 + s1.gpr .r11 + _) = _
        rw [e11, u1.other _ (by decide), hc.r0, ea2 hfit (by omega)])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hc.inR (by omega)) fun s3 u3 => ?_
  have e1 : s3.gpr .r1 = BitVec.ofNat 32 (bit k (n - 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, hcur.stp.frame _ fun r hr => ?_, Nat.add_comm, hbits _ (by omega)]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, toNat_imm (by omega)]; omega
    · rw [List.mem_singleton.mp hr]
      exact fun h => by
        simp only [Region.Contains] at h
        rw [Offset.sub_toNat _ (by omega) (by omega)] at h
        have := ACC_eq
        omega
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have e10 : s4.gpr .r10 = BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u4.gpr]; show s3.gpr .r10 ^^^ s3.gpr .r1 = _
    rw [e1, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hcur.r10,
      ofNat_xor (by omega) (by omega)]
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have e9 : s6.gpr .r9 = 0 - BitVec.ofNat 32 ((ladderAfter k x1 n).swap ^^^ bit k (n - 1)) := by
    rw [u6.gpr]; show s5.gpr .r9 - s5.gpr .r10 = _
    rw [u5.gpr, u5.other _ (by decide), e10]
  have hr6 : Rest [.r1, .r9, .r10, .r11] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hc6 : Ctx b s6 := hc.of_rest hr6 (by decide)
  have hS6 : SlotsOk s6.mem (State.addr b) LQ (ladV x1 (ladderAfter k x1 n)) := by
    rw [hm6]; exact hcur.slots
  refine WP.append (cswapS (acc := ACC) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc6 hx e9 hS6)
    fun s7 ⟨hr7, hf7, hS7⟩ => ?_
  have hc7 : Ctx b s7 := hc6.of_rest hr7 (by decide)
  refine WP.append (cswapS (acc := ACC) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc7 hx
    (by rw [hr7.gpr _ (by decide), e9]) hS7) fun s8 ⟨hr8, hf8, hS8⟩ => ?_
  refine wp_mov (op2_reg _ _) fun s9 u9 => WP.block_nil ?_
  have hr9 : Rest [.r1, .r2, .r3, .r4, .r9, .r10, .r11] s s9 :=
    (hr6.mono (by decide)).trans ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
      (u9.rest (by decide))))
  exact ⟨hc.of_rest hr9 (by decide),
    hcur.stp.trans ⟨hr9.mono (by decide), by rw [u9.mem, ← hm6]; exact hf7.trans hf8⟩,
    by rw [u9.gpr, hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), e1],
    by rw [u9.other _ (by decide), hr8.gpr _ (by decide), hr7.gpr _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e11],
    by rw [u9.mem]; exact hS8⟩

theorem sub0 (x : BitVec 32) : x - 0 = x := by simp

theorem step_eq : step = .seq (.block stepHead) (opsCode ladOps (.block [.cmp .r11 (.imm 0)])) := rfl

theorem step_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {sL : State} (hbits : Bits b k sL.mem)
    {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 255) {s : State} (h : LadInv b k x1 sL n s) :
    WP isa step s fun s' => LadInv b k x1 sL (n - 1) s' ∧ s'.z = decide (n - 1 = 0) := by
  rw [step_eq]
  refine WP.seq (WP.mono (head_ok hbits hn hn' h) fun s1 h1 =>
    ops_ok ladOps LQ _ s1 ladOps_ok h1 fun s2 h2 => ?_)
  refine wp_cmp (op2_imm (by decide)) fun s3 u3 hz => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h2.ctx.of_rest (u3.rest []) (by decide)
  · exact h2.stp.trans (Stp.of_rest (u3.rest []) (by decide) u3.mem)
  · rw [u3.gpr, h2.r10, ladderAfter_step k x1 (show n - 1 < 255 by omega), Nat.sub_add_cancel hn,
      ladderStep_eq]
  · rw [u3.gpr, h2.r11]
  · rw [u3.mem]
    refine (h2.slots.mono (by decide)).congr fun q hq => ?_
    rw [ladderAfter_step k x1 (show n - 1 < 255 by omega), Nat.sub_add_cancel hn]
    exact ladOps_vals k x1 _ (n - 1) q hq
  · rw [hz, h2.r11, sub0, ofNat_beq_zero (by omega)]

/-- The ladder, from the state with the bits of the scalar in `BITS` and the
initial elements in `LQ`. -/
theorem ladder_ok {b : BitVec 32} {k : Nat} {x1 : Fe} {s : State} (hc : Ctx b s) (hbits : Bits b k s.mem)
    (hS : SlotsOk s.mem (State.addr b) LQ (ladV x1 (VG.Proof.X25519.init x1))) :
    WP isa ladder s fun s' => Stp b s s' ∧ Ctx b s' ∧
      s'.gpr .r10 = BitVec.ofNat 32 (ladderAfter k x1 0).swap ∧
      SlotsOk s'.mem (State.addr b) LQ (ladV x1 (ladderAfter k x1 0)) := by
  unfold ladder
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    WP.block_nil ?_)
  have hr2 : Rest [.r10, .r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hbits2 : Bits b k s2.mem := by rw [hm2]; exact hbits
  have h255 : LadInv b k x1 s2 255 s2 :=
    ⟨⟨hc.of_rest hr2 (by decide), Stp.refl _ _, by rw [u2.gpr]; rfl,
      by rw [u2.other _ (by decide), u1.gpr]; rfl, by rw [hm2]; exact hS⟩⟩
  have hst : Stp b s s2 := Stp.of_rest hr2 (by decide) hm2
  refine WP.mono (Q := LadInv b k x1 s2 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 255 ∧ LadInv b k x1 s2 m s') ?_ 255 s2 ⟨by decide, Nat.le_refl _, h255⟩)
    fun s' ⟨h'⟩ => ⟨hst.trans h'.stp, h'.ctx, h'.r10, h'.slots⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (step_ok hbits2 h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_ne, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_ne, hz]; simp [hm], m - 1, by omega, by omega, by omega, hl'⟩

end VG.Proof.X25519.Arm
