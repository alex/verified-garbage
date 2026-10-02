import VerifiedGarbage.Proof.X25519.X86.Ops
import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.Framework.X86.Spill

/-!
# X25519 on x86 (32-bit): the ladder

What holds from the end of the setup on (`Base`: the working space, the saved
registers, the scalar's bits, and that nothing outside the working space
changes), and the ladder: each iteration takes the ladder's state after the
bits `254, …, n + 1` in the slots `X2, Z2, X3, Z3` and the word `SWAP` (`LInv
(n + 1)`) to that after the bit `n` (`LInv n`).
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The callee-saved registers and their slots in the working space, in the
order `save` stores them. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ savedSlots, p.2 + 4 ≤ 16 := by decide

/-- What holds from the end of the setup on: the working space at `x` (in
`edi`), the saved registers (of the state on entry `s₀`), the bits of the
scalar `k`, and memory outside the working space as on entry. -/
structure Base (x : BitVec 32) (k : Nat) (s₀ s : State) : Prop where
  ctx : Ctx x s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR x] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr savedSlots
  bits : ∀ t < 255, s.mem (addr x (BITS + t)) = BitVec.ofNat 8 (bit k t)

/-- A byte of the working space outside a frame's region. -/
theorem byte_frame1 {m m' : Mem} {x : BitVec 32} {o n d : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (ho : o + n ≤ 4096) (hd : d < 4096) (h : d + 1 ≤ o ∨ o + n ≤ d) :
    m' (addr x d) = m (addr x d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact sub_disj (x := x) (n := 1) (by omega_using [hx, hd]) (by omega_using [hx, ho]) h _
      (Region.contains_self _ _)

theorem Base.of_frame {x : BitVec 32} {k : Nat} {s₀ s s' : State} (h : Base x k s₀ s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {o n : Nat} (hf : Frame [sub x o n] s.mem s'.mem) (ho : o + n ≤ 4096)
    (hlo : 16 ≤ o) (hgap : o + n ≤ 32 ∨ 288 ≤ o) (hon : o < 4096) : Base x k s₀ s' := by
  have hfit := h.ctx.fit
  refine ⟨h.ctx.keep hedi hwr, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_, fun t ht => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, scR_eq]
      exact sub_sub hfit (Nat.zero_le _) (by omega_using [ho]) hon⟩)
  · have := savedSlots_bound p hp
    exact wd_frame1 hf hfit ho (by omega_using [this]) (by omega_using [this, hlo])
  · rw [byte_frame1 hf hfit ho (by simp only [BITS]; omega_using [ht]) (by simp only [BITS]; omega_using [ht, hgap])]
    exact h.bits t ht

/-- The operations keep `Base`. -/
theorem Base.ops {x : BitVec 32} {k : Nat} {s₀ s s' : State} (h : Base x k s₀ s) (hk : Keep s s')
    (hf : Frame [sub x 288 640] s.mem s'.mem) : Base x k s₀ s' :=
  h.of_frame hk.edi hk.esp hk.rd hk.wr hf (by decide) (by decide) (.inr (Nat.le_refl _)) (by decide)

/-- The ladder's state after the bits `254` down to `n`, in the slots. -/
structure LInv (x : BitVec 32) (k : Nat) (x1 : Fe) (s₀ : State) (n : Nat) (s : State) : Prop
    extends Base x k s₀ s where
  esi : s.gpr .esi = BitVec.ofNat 32 n
  vx1 : F s.mem x X1 = x1
  vx2 : F s.mem x X2 = (ladderAfter k x1 n).x2
  vz2 : F s.mem x Z2 = (ladderAfter k x1 n).z2
  vx3 : F s.mem x X3 = (ladderAfter k x1 n).x3
  vz3 : F s.mem x Z3 = (ladderAfter k x1 n).z3
  swap : wd s.mem x SWAP = BitVec.ofNat 32 (ladderAfter k x1 n).swap

theorem run_step (V : Nat → Fe) :
    let A := V X2 + V Z2
    let AA := A * A
    let B := V X2 - V Z2
    let BB := B * B
    let Ee := AA - BB
    let C := V X3 + V Z3
    let D := V X3 - V Z3
    let DA := D * A
    let CB := C * B
    run stepOps V X2 = AA * BB ∧ run stepOps V Z2 = Ee * (AA + a24 * Ee) ∧
      run stepOps V X3 = (DA + CB) * (DA + CB) ∧ run stepOps V Z3 = V X1 * ((DA - CB) * (DA - CB)) ∧
      run stepOps V X1 = V X1 := by
  simp only [run, stepOps, opOut, opVal, Function.update_apply, X1, X2, Z2, X3, Z3, A, B, C, D, AA, BB,
    Impl.X25519.X86.E, DA, CB]
  simp (config := {decide := true}) only [ite_true, ite_false]

theorem stepOps_valid : ∀ op ∈ stepOps, opValid op = true := by decide

theorem cswap_fst (sw : Nat) (a b : Fe) : (Spec.X25519.cswap sw a b).1 = if sw = 1 then b else a := by
  unfold Spec.X25519.cswap; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Fe) : (Spec.X25519.cswap sw a b).2 = if sw = 1 then a else b := by
  unfold Spec.X25519.cswap; split <;> rfl

theorem F_ite {m m' : Mem} {x : BitVec 32} {q a b : Nat} (sw : Nat)
    (h : fe m' x q = if sw = 1 then fe m x a else fe m x b) :
    F m' x q = if sw = 1 then F m x a else F m x b := by
  simp only [F, h]; split <;> rfl

theorem ofNat_xor {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = BitVec.ofNat 32 (a ^^^ b) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem byte_ofNat {b : Nat} (h : b ≤ 1) : (BitVec.ofNat 8 b).setWidth 32 = BitVec.ofNat 32 b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> decide

theorem xor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem addr_add_ofNat (x : BitVec 32) (n d : Nat) : addr (x + BitVec.ofNat 32 n) d = addr x (d + n) := by
  simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm n d]

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_movzx8 {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {o : Nat} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Wp.Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Wp.Upd.setReg _ _ _))
  simp only [exec, State.load8, ea_mk, ha, hin, ↓reduceIte, Option.map_some]

/-- The start of an iteration: the counter decremented to `n`, `swap` updated
and the mask of the swap in `ecx`. -/
theorem stepHead_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} {n : Nat} (hn : n < 255)
    (h : LInv x k x1 s₀ (n + 1) s) :
    WP isa (.block stepHead) s fun s' => Base x k s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 n ∧
      s'.gpr .ecx = mask ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n) ∧
      (∀ q, isSlot q = true → F s'.mem x q = F s.mem x q) ∧
      wd s'.mem x SWAP = BitVec.ofNat 32 (bit k n) := by
  have hc := h.ctx
  have hfit := hc.fit
  have hsw := ladderAfter_swap_le k x1 (n := n + 1) (by omega_using [hn])
  have hb := bit_le k n
  refine Wp.wp_subi fun s₁ u₁ _ _ => Wp.wp_mov fun s₂ u₂ => Wp.wp_add fun s₃ u₃ _ => ?_
  have esi₁ : s₁.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₁.gpr, h.esi]; exact Wp.ofNat_pred (by omega_using [])
  have esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), esi₁]
  have eax₃ : s₃.gpr .eax = x + BitVec.ofNat 32 n := by
    rw [u₃.gpr, u₂.gpr, u₂.other .esi (by decide), esi₁, u₁.other _ (by decide), hc.edi]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have edi₃ : s₃.gpr .edi = x := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  have c₃ : Ctx x s₃ := hc.keep (by rw [edi₃, hc.edi]) (by rw [u₃.wr, u₂.wr, u₁.wr])
  refine wp_movzx8 (a := addr x (BITS + n)) (by rw [eax₃, addr_add_ofNat])
    (c₃.inRW (by simp only [BITS]; omega_using [hn]) (by decide)) fun s₄ u₄ => ?_
  have eax₄ : s₄.gpr .eax = BitVec.ofNat 32 (bit k n) := by
    rw [u₄.gpr, m₃, h.bits n (by omega_using [hn]), byte_ofNat hb]
  have c₄ := (updKeep u₄).ctx c₃
  refine Wp.wp_ldm c₄.edi (c₄.inRW (by simp only [SWAP]; decide) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_xor fun s₆ u₆ => ?_
  have edx₆ : s₆.gpr .edx = BitVec.ofNat 32 ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n) := by
    rw [u₆.gpr, u₅.gpr, u₄.mem, m₃, u₅.other .eax (by decide), eax₄]
    exact (congrArg (· ^^^ _) h.swap).trans (ofNat_xor hsw hb)
  have c₆ := (updKeep u₆).ctx ((updKeep u₅).ctx c₄)
  refine Wp.wp_stm c₆.edi (c₆.inW (by simp only [SWAP]; decide) (by decide)) fun s₇ u₇ => ?_
  refine Wp.wp_movi fun s₈ u₈ => Wp.wp_sub fun s₉ u₉ _ => WP.block_nil ?_
  have m₇ : s₉.mem = s.mem.writeW (addr x SWAP) (BitVec.ofNat 32 (bit k n)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.other .eax (by decide), u₅.other .eax (by decide), eax₄, u₆.mem,
      u₅.mem, u₄.mem, m₃]
  have hf : Frame [sub x SWAP 4] s.mem s₉.mem := by
    rw [m₇]; exact frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  have g : ∀ r, r ≠ .ecx → r ≠ .eax → r ≠ .edx → r ≠ .esi → s₉.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₉.other _ h1, u₈.other _ h1, u₇.gpr, u₆.other _ h3, u₅.other _ h3, u₄.other _ h2, u₃.other _ h2,
      u₂.other _ h2, u₁.other _ h4]
  refine ⟨h.toBase.of_frame (g _ (by decide) (by decide) (by decide) (by decide))
    (g _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) hf (by decide) (by decide)
    (.inl (by decide)) (by decide), ?_, ?_, fun q hq => ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
  · rw [u₉.gpr, u₈.gpr, u₈.other .edx (by decide), u₇.gpr, edx₆]; rfl
  · have hq' := slot_ge hq; have hqb := slot_below hq; simp only [Below, T] at hqb
    simp only [F]
    exact congrArg toFe (fe_frame fun j hj => wd_frame1 hf hfit (by decide) (by omega_using [hqb, hj])
      (by simp only [SWAP]; omega_using [hq']))
  · rw [m₇, wd_write_self]

/-- A frame of two slots is one of the slots and `T`. -/
theorem frame2_wide {m m' : Mem} {x : BitVec 32} {a b : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x a 32, sub x b 32] m m') (ha : isSlot a = true) (hb : isSlot b = true) :
    Frame [sub x 288 640] m m' := by
  have ha1 := slot_ge ha; have ha2 := slot_below ha; have hb1 := slot_ge hb; have hb2 := slot_below hb
  simp only [Below, T] at ha2 hb2
  exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_sub hx ha1 (by omega_using [ha2]) (by omega_using [ha2])
    · exact sub_sub hx hb1 (by omega_using [hb2]) (by omega_using [hb2])⟩

/-- A slot other than the two a frame's regions are. -/
theorem F_frame2 {m m' : Mem} {x : BitVec 32} {a b q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x a 32, sub x b 32] m m') (ha : isSlot a = true) (hb : isSlot b = true)
    (hq : isSlot q = true) (hqa : q ≠ a) (hqb : q ≠ b) : F m' x q = F m x q := by
  have ha2 := slot_below ha; have hb2 := slot_below hb; have hq2 := slot_below hq
  simp only [Below, T] at ha2 hb2 hq2
  have sa := slot_ne ha hq hqa; have sb := slot_ne hb hq hqb
  simp only [F]
  refine congrArg toFe (fe_frame fun j hj => wd_frame hf fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega_using [hx, hq2, hj]) (by omega_using [hx, ha2]) (by omega_using [sa, hj])
  · exact sub_disj (by omega_using [hx, hq2, hj]) (by omega_using [hx, hb2]) (by omega_using [sb, hj])

/-- One iteration of the ladder, for the bit `n`. -/
theorem step_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} {n : Nat} (hn : n < 255)
    (h : LInv x k x1 s₀ (n + 1) s) :
    WP isa (.block step) s fun s' => LInv x k x1 s₀ n s' ∧ s'.zf = some (decide (n = 0)) := by
  have hfit := h.ctx.fit
  have hsw := xor_le_one (ladderAfter_swap_le k x1 (n := n + 1) (by omega_using [hn])) (bit_le k n)
  simp only [step, List.append_assoc]
  refine WP.block_append (WP.mono (stepHead_ok hn h) fun s₁ ⟨b₁, esi₁, ecx₁, F₁, sw₁⟩ => ?_)
  refine WP.block_append (WP.mono (cswap_ok b₁.ctx (X := X2) (Y := X3) (by decide) (by decide) (by decide)
    hsw ecx₁) fun s₂ ⟨k₂, ecx₂, f₂, x₂, y₂⟩ => ?_)
  have b₂ := b₁.ops k₂ (frame2_wide hfit f₂ (by decide) (by decide))
  refine WP.block_append (WP.mono (cswap_ok b₂.ctx (X := Z2) (Y := Z3) (by decide) (by decide) (by decide)
    hsw (ecx₂.trans ecx₁)) fun s₃ ⟨k₃, _, f₃, x₃, y₃⟩ => ?_)
  have b₃ := b₂.ops k₃ (frame2_wide hfit f₃ (by decide) (by decide))
  refine WP.block_append (WP.mono (ops_ok stepOps b₃.ctx stepOps_valid) fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  have b₄ := b₃.ops k₄ f₄
  refine Wp.wp_test fun s₅ u₅ z₅ => WP.block_nil ?_
  -- The values after the swaps.
  have hstep := ladderAfter_step k x1 hn
  have v₁ : ∀ q, isSlot q = true → F s₁.mem x q = F s.mem x q := F₁
  have eX2 : F s₃.mem x X2 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).x2 (ladderAfter k x1 (n + 1)).x3).1 := by
    rw [F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide), F_ite _ x₂,
      v₁ _ (by decide), v₁ _ (by decide), h.vx2, h.vx3, cswap_fst]
  have eX3 : F s₃.mem x X3 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).x2 (ladderAfter k x1 (n + 1)).x3).2 := by
    rw [F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide), F_ite _ y₂,
      v₁ _ (by decide), v₁ _ (by decide), h.vx2, h.vx3, cswap_snd]
  have eZ2 : F s₃.mem x Z2 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).z2 (ladderAfter k x1 (n + 1)).z3).1 := by
    rw [F_ite _ x₃, F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      v₁ _ (by decide), v₁ _ (by decide), h.vz2, h.vz3, cswap_fst]
  have eZ3 : F s₃.mem x Z3 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).z2 (ladderAfter k x1 (n + 1)).z3).2 := by
    rw [F_ite _ y₃, F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      v₁ _ (by decide), v₁ _ (by decide), h.vz2, h.vz3, cswap_snd]
  have eX1 : F s₃.mem x X1 = x1 := by
    rw [F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide), v₁ _ (by decide), h.vx1]
  obtain ⟨r2, rz2, r3, rz3, r1⟩ := run_step (F s₃.mem x)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  refine ⟨⟨b₄.of_frame (o := 288) (n := 640) (by rw [u₅.gpr]) (by rw [u₅.gpr]) u₅.rd u₅.wr
    (by rw [m₅]; exact Frame.refl _ _) (by decide) (by decide) (.inr (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.gpr, k₄.esi, k₃.esi, k₂.esi, esi₁]
  · rw [m₅, e₄ _ (by decide), r1, eX1]
  · rw [m₅, e₄ _ (by decide), r2, hstep, ladderStep_eq, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), rz2, hstep, ladderStep_eq, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), r3, hstep, ladderStep_eq, eX3, eZ3, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), rz3, hstep, ladderStep_eq, eX3, eZ3, eX2, eZ2, eX1]
  · have hs : ∀ {m m' : Mem}, Frame [sub x 288 640] m m' → wd m' x SWAP = wd m x SWAP := fun hf =>
      wd_frame1 hf hfit (by decide) (by decide) (.inl (by decide))
    rw [m₅, hs f₄, hs (frame2_wide hfit f₃ (by decide) (by decide)),
      hs (frame2_wide hfit f₂ (by decide) (by decide)), sw₁, hstep, ladderStep_eq]
  · rw [z₅, k₄.esi, k₃.esi, k₂.esi, esi₁, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- The 255 iterations. -/
theorem ladderLoop_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} (h : LInv x k x1 s₀ 255 s) :
    WP isa (.loop (.block step) .ne) s (LInv x k x1 s₀ 0) := by
  refine WP.loop (M := isa) (Q := LInv x k x1 s₀ 0) (fun m s => 1 ≤ m ∧ m ≤ 255 ∧ LInv x k x1 s₀ m s)
    (fun m s hm => ?_) 255 s ⟨by decide, Nat.le_refl _, h⟩
  obtain ⟨h1, h2, hL⟩ := hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (step_ok (by omega_using [h2]) hL) fun s' ⟨hL', hz⟩ => ?_
  by_cases e : n = 0
  · subst e
    exact .inl ⟨by simp only [eval, hz]; rfl, hL'⟩
  · exact .inr ⟨by simp only [eval, hz, e, decide_false]; rfl, n, by omega_using [],
      by omega_using [e], by omega_using [h2], hL'⟩

end VG.Proof.X25519.X86
