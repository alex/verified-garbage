import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Correct

/-!
# ChaCha20-Poly1305 on x86 (32-bit): constant time

Untrusted: everything here is checked by Lean.

The x86 taint analysis does not analyse calls or frames, so the two runs
are related piece by piece (`RelCT`), as for `vg_chacha20_xor`: the taint
analysis proves each straight-line piece and the copy loop constant time
(`taintRel`), from the registers that the correctness proof says hold the
same public values in both runs (the pointers, the lengths and `esp`); each
call of a verified function in a frame of its arguments is constant time by
the callee's own proof (`RelCT.callWith`), its arguments being public; the
branch on the length of the tail is on a public value (`RelCT.ite`). What
each run satisfies between the pieces comes from the correctness proof
(`RelCT.post`).
-/

namespace VG.Proof.ChaCha20Poly1305.X86

open VG VG.X86 VG.Impl.ChaCha20Poly1305.X86
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86.Xor (τr agree_regs relct_nil)

/-! ## Tools -/

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : Taint.Hint taint.T}
    (h : (taint.check (τr rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (τr rs) (fun x y hp => agree_regs (hr x y hp)) h

/-- The final states of two runs related by `P` satisfy what correctness
says of each. -/
theorem RelCT.post {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x F₁ ∧ WP isa c y F₂) :
    RelCT isa P c fun x y => F₁ x ∧ F₂ y :=
  RelCT.mono (RelCT.wp h hw) (fun _ _ h => h) fun _ _ h => h.2

/-- Two entry states that agree on the public data. -/
structure Pub (a b : State) : Prop where
  esp : b.gpr .esp = a.gpr .esp
  args : ∀ i < 5, arg b i = arg a i

theorem Pub.of {a b : State} (h : pubX86 a b) : Pub a b := ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

section
variable {a b : State} (hq : Pub a b)
include hq

theorem Pub.cx : arg b 0 = arg a 0 := hq.args 0 (by omega)
theorem Pub.a1 : arg b 1 = arg a 1 := hq.args 1 (by omega)
theorem Pub.a2 : arg b 2 = arg a 2 := hq.args 2 (by omega)
theorem Pub.a3 : arg b 3 = arg a 3 := hq.args 3 (by omega)
theorem Pub.a4 : arg b 4 = arg a 4 := hq.args 4 (by omega)

/-- The registers holding the same public values in both runs. -/
theorem Pub.inv {x y : State} (hx : Inv a x) (hy : Inv b y) :
    ∀ r ∈ [Reg.edi, .esp], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx.edi, hy.edi]; exact hq.cx.symm
  · rw [hx.esp, hy.esp]; exact hq.esp.symm

theorem Pub.fin {x y : State} (hx : Fin a x) (hy : Fin b y) :
    ∀ r ∈ [Reg.edi, .esp], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx.edi, hy.edi]; exact hq.cx.symm
  · rw [hx.at_.esp, hy.at_.esp]; exact hq.esp.symm

theorem Pub.c32 (k : Nat) : C32 b k = C32 a k := by simp only [C32, CX, hq.cx]

theorem Pub.at_ {x y : State} (hx : At a x) (hy : At b y) : x.gpr .esp = y.gpr .esp := by
  rw [hx.esp, hy.esp]; exact hq.esp.symm

end

/-- The callee's public data: `esp` and the arguments, which are the
registers pushed. -/
theorem entry_pub {rs : List Reg} {x y : State} (rd wr : List Region) (hrs : Reg.esp ∉ rs)
    (hfit : 4 * rs.length + 4 ≤ (x.gpr .esp).toNat) (hsp : x.gpr .esp = y.gpr .esp)
    (hr : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ((pushed rs x).callEntry.withRegions rd wr).gpr .esp = ((pushed rs y).callEntry.withRegions rd wr).gpr .esp ∧
    ∀ i < rs.length, arg ((pushed rs x).callEntry.withRegions rd wr) i =
      arg ((pushed rs y).callEntry.withRegions rd wr) i :=
  ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp],
   fun i hi => by simp only [arg_withRegions]; exact callEntry_arg_eq hrs hfit hsp hr hi⟩

theorem regs_eq {x y : State} {rs : List Reg} (h : ∀ r ∈ rs, x.gpr r = y.gpr r) :
    ∀ r ∈ rs, x.gpr r = y.gpr r := h

/-! ## The calls -/

section
variable {a b : State} (ha : APre a) (hb : APre b) (hq : Pub a b)
include ha hb hq

theorem block_rel :
    RelCT isa (fun x y => Pro2 a x ∧ Pro2 b y)
      (callWith [.edx, .ecx] "vg_chacha20_block" Impl.ChaCha20.X86.block) fun _ _ => True :=
  RelCT.callWith Proof.ChaCha20.X86.block_verified.1 Proof.ChaCha20.X86.block_verified.2.1 (rdBlk a) (wrBlk a)
    fun x y ⟨hx, hy⟩ => by
      have py := block_pre hb hy.at_ hy.ecx hy.edx
      rw [show rdBlk b = rdBlk a by simp only [rdBlk, sub, cx, CX, E, hq.cx, hq.esp],
        show wrBlk b = wrBlk a by simp only [wrBlk, sub, cx, CX, hq.cx]] at py
      have fit := hx.at_.fit ha (rs := [.edx, .ecx]) (by decide)
      have p := entry_pub (rdBlk a) (wrBlk a) (by decide) fit (hq.at_ hx.at_ hy.at_) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hx.edx, hy.edx, hq.c32]
        · rw [hx.ecx, hy.ecx, hq.c32])
      exact ⟨fit, block_pre ha hx.at_ hx.ecx hx.edx, py, hq.at_ hx.at_ hy.at_, p.1, p.2 0 (by decide),
        p.2 1 (by decide)⟩

theorem init_rel :
    RelCT isa (fun x y => Pro4 a x ∧ Pro4 b y)
      (callWith [.ecx, .edx] "vg_poly1305_init" Impl.Poly1305.X86.init) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.init_verified.1 Proof.Poly1305.X86.init_verified.2.1 (rdInit a) (wrInit a)
    fun x y ⟨hx, hy⟩ => by
      have py := init_pre hb hy.at_ hy.ecx hy.edx
      rw [show rdInit b = rdInit a by simp only [rdInit, sub, cx, CX, E, hq.cx, hq.esp],
        show wrInit b = wrInit a by simp only [wrInit, sub, cx, CX, hq.cx]] at py
      have fit := hx.at_.fit ha (rs := [.ecx, .edx]) (by decide)
      have p := entry_pub (rdInit a) (wrInit a) (by decide) fit (hq.at_ hx.at_ hy.at_) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.edx, hy.edx, hq.c32])
      exact ⟨fit, init_pre ha hx.at_ hx.ecx hx.edx, py, hq.at_ hx.at_ hy.at_, p.1, p.2 0 (by decide),
        p.2 1 (by decide)⟩

theorem oneB_rel {k : Nat} (hk : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024)) :
    RelCT isa (fun x y => OneA a k x ∧ OneA b k y)
      (callWith [.eax, .ecx, .edx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.blocks_verified.1 Proof.Poly1305.X86.blocks_verified.2.1
    (rdBlocks a (C32 a k) 1) (wrBlocks a) fun x y ⟨hx, hy⟩ => by
      have py := blocks_pre hb hy.inv.at (n := 1) (by decide) (bsrc_ctx hb hk) hy.edx hy.ecx hy.eax
      rw [show rdBlocks b (C32 b k) 1 = rdBlocks a (C32 a k) 1 by simp only [rdBlocks, E, hq.c32, hq.esp],
        show wrBlocks b = wrBlocks a by simp only [wrBlocks, sub, cx, CX, hq.cx]] at py
      have fit := hx.inv.at.fit ha (rs := [.eax, .ecx, .edx]) (by decide)
      have p := entry_pub (rdBlocks a (C32 a k) 1) (wrBlocks a) (by decide) fit (hq.at_ hx.inv.at hy.inv.at) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.eax, hy.eax]
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.edx, hy.edx, hq.c32])
      exact ⟨fit, blocks_pre ha hx.inv.at (n := 1) (by decide) (bsrc_ctx ha hk) hx.edx hx.ecx hx.eax, py,
        hq.at_ hx.inv.at hy.inv.at, p.1, p.2 0 (by decide), p.2 1 (by decide), p.2 2 (by decide)⟩

theorem maB_rel {i : Nat} (hi : i + 1 < 5) (hsa : Src a (arg a i) (arg a (i + 1)).toNat)
    (hsb : Src b (arg b i) (arg b (i + 1)).toNat) :
    RelCT isa (fun x y => MA a i x ∧ MA b i y)
      (callWith [.eax, .ebx, .ecx] "vg_poly1305_blocks" Impl.Poly1305.X86.blocks) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.blocks_verified.1 Proof.Poly1305.X86.blocks_verified.2.1
    (rdBlocks a (arg a i) ((arg a (i + 1)).toNat / 16)) (wrBlocks a) fun x y ⟨hx, hy⟩ => by
      have ei : arg b i = arg a i := hq.args i (by omega)
      have ei' : arg b (i + 1) = arg a (i + 1) := hq.args (i + 1) hi
      have py := blocks_pre hb hy.inv.at (by decide) (hsb.bsrc (Nat.mul_div_le _ _)) hy.ecx hy.ebx hy.eax
      rw [show rdBlocks b (arg b i) ((arg b (i + 1)).toNat / 16) =
          rdBlocks a (arg a i) ((arg a (i + 1)).toNat / 16) by simp only [rdBlocks, E, ei, ei', hq.esp],
        show wrBlocks b = wrBlocks a by simp only [wrBlocks, sub, cx, CX, hq.cx]] at py
      have fit := hx.inv.at.fit ha (rs := [.eax, .ebx, .ecx]) (by decide)
      have p := entry_pub (rdBlocks a (arg a i) ((arg a (i + 1)).toNat / 16)) (wrBlocks a) (by decide) fit
        (hq.at_ hx.inv.at hy.inv.at) (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [hx.eax, hy.eax, ei']
          · rw [hx.ebx, hy.ebx, ei]
          · rw [hx.ecx, hy.ecx, hq.c32])
      exact ⟨fit, blocks_pre ha hx.inv.at (by decide) (hsa.bsrc (Nat.mul_div_le _ _)) hx.ecx hx.ebx hx.eax, py,
        hq.at_ hx.inv.at hy.inv.at, p.1, p.2 0 (by decide), p.2 1 (by decide), p.2 2 (by decide)⟩

theorem crB_rel :
    RelCT isa (fun x y => CrA a x ∧ CrA b y)
      (callWith [.esi, .edx, .ecx, .eax] "vg_chacha20_xor" Impl.ChaCha20.X86.Xor.xor) fun _ _ => True :=
  RelCT.callWith Proof.ChaCha20.X86.Xor.xor_verified.1 Proof.ChaCha20.X86.Xor.xor_verified.2.1 [] (wrXor a)
    fun x y ⟨hx, hy⟩ => by
      have py := xor_pre hb hy.inv.at hy.eax hy.ecx hy.edx hy.esi
      rw [show wrXor b = wrXor a by simp only [wrXor, sub, cx, CX, dR, dp, DP, L, LN, E, hq.cx, hq.a3, hq.a4,
        hq.esp]] at py
      have fit := hx.inv.at.fit ha (rs := [.esi, .edx, .ecx, .eax]) (by decide)
      have p := entry_pub [] (wrXor a) (by decide) fit (hq.at_ hx.inv.at hy.inv.at) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hx.esi, hy.esi, hq.c32]
        · rw [hx.edx, hy.edx]; exact hq.a4.symm
        · rw [hx.ecx, hy.ecx]; exact hq.a3.symm
        · rw [hx.eax, hy.eax, hq.c32])
      exact ⟨fit, xor_pre ha hx.inv.at hx.eax hx.ecx hx.edx hx.esi, py, hq.at_ hx.inv.at hy.inv.at, p.1,
        fun i hi => p.2 i hi⟩

theorem fiB_rel {out : Nat} (ho : OutOk out) :
    RelCT isa (fun x y => FiA a out x ∧ FiA b out y)
      (callWith [.ecx, .eax, .edx, .esi] "vg_poly1305_finalize" Impl.Poly1305.X86.finalize) fun _ _ => True :=
  RelCT.callWith Proof.Poly1305.X86.finalize_verified.1 Proof.Poly1305.X86.finalize_verified.2.1 (rdFin a)
    (wrFin a out) fun x y ⟨hx, hy⟩ => by
      have py := finalize_pre hb hy.inv.at ho hy.ecx hy.eax hy.edx hy.esi
      rw [show rdFin b = rdFin a by simp only [rdFin, sub, cx, CX, E, hq.cx, hq.esp],
        show wrFin b out = wrFin a out by simp only [wrFin, sub, cx, CX, hq.cx]] at py
      have fit := hx.inv.at.fit ha (rs := [.ecx, .eax, .edx, .esi]) (by decide)
      have p := entry_pub (rdFin a) (wrFin a out) (by decide) fit (hq.at_ hx.inv.at hy.inv.at) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.eax, hy.eax]
        · rw [hx.edx, hy.edx, hq.c32]
        · rw [hx.esi, hy.esi, hq.c32])
      exact ⟨fit, finalize_pre ha hx.inv.at ho hx.ecx hx.eax hx.edx hx.esi, py, hq.at_ hx.inv.at hy.inv.at, p.1,
        p.2 0 (by decide), p.2 1 (by decide), p.2 2 (by decide), p.2 3 (by decide)⟩

/-! ## The parts -/

theorem prologue_rel :
    RelCT isa (fun x y => x = a ∧ y = b) prologue fun x y => PostP a x ∧ PostP b y := by
  rw [prologue_eq]
  refine RelCT.seq (R := fun x y => x = a.setReg .eax (CX a) ∧ y = b.setReg .eax (CX b))
    (RelCT.post (taintRel [.esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr hx hy; exact hq.esp.symm) (by taint_decide))
      fun x y ⟨hx, hy⟩ => by subst hx hy; exact ⟨load_ok ha, load_ok hb⟩) ?_
  refine RelCT.seq (R := fun x y => Pro2 a x ∧ Pro2 b y)
    (RelCT.post (taintRel [.eax, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hx hy
      rcases hr with rfl | rfl
      · simp only [State.setReg, ite_true]; exact hq.cx.symm
      · simp (config := {decide := true}) only [State.setReg, ite_false]; exact hq.esp.symm) (by taint_decide))
      fun x y ⟨hx, hy⟩ => by subst hx hy; exact ⟨pro2_ok ha, pro2_ok hb⟩) ?_
  refine RelCT.seq (R := fun x y => Pro3 a x ∧ Pro3 b y)
    (RelCT.post (block_rel ha hb hq) fun x y ⟨hx, hy⟩ => ⟨pro3_ok ha hx, pro3_ok hb hy⟩) ?_
  refine RelCT.seq (R := fun x y => Pro4 a x ∧ Pro4 b y)
    (RelCT.post (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hx.edi, hy.edi]; exact hq.cx.symm
      · exact hq.at_ hx.at_ hy.at_) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨pro4_ok hx, pro4_ok hy⟩) ?_
  exact RelCT.post (init_rel ha hb hq) fun x y ⟨hx, hy⟩ => ⟨post_ok ha hx, post_ok hb hy⟩

theorem absorbOne_rel {k : Nat} (hk : k = 576 ∨ k = 656) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) (absorbOne k) fun _ _ => True := by
  have hk' : k + 16 ≤ 448 ∨ (576 ≤ k ∧ k + 16 ≤ 1024) := by omega
  rw [absorbOne_eq]
  refine RelCT.seq (R := fun x y => OneA a k x ∧ OneA b k y)
    (RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨WP.mono (oneA_ok hx k) fun _ h => h.1,
      WP.mono (oneA_ok hy k) fun _ h => h.1⟩) (oneB_rel ha hb hq hk')
  rcases hk with rfl | rfl <;>
  exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide)

/-- After the tail's start is computed and the block zeroed. -/
def PDz (s₀ : State) (i : Nat) (s : State) : Prop :=
  PD s₀ i s ∧ ∀ j < 16, s.mem (cx s₀ + BitVec.ofNat 64 (576 + j)) = 0

theorem padTail_rel {i : Nat} (hsa : Src a (arg a i) (arg a (i + 1)).toNat)
    (hsb : Src b (arg b i) (arg b (i + 1)).toNat) (hi : i + 1 < 5) (h0 : (arg a (i + 1)).toNat % 16 ≠ 0) :
    RelCT isa (fun x y => MC a i x ∧ MC b i y) padTail fun _ _ => True := by
  have ei : arg b i = arg a i := hq.args i (by omega)
  have ei' : arg b (i + 1) = arg a (i + 1) := hq.args (i + 1) hi
  have h0' : (arg b (i + 1)).toNat % 16 ≠ 0 := by rw [ei']; exact h0
  rw [padTail_eq]
  refine RelCT.seq (R := fun x y => PDz a i x ∧ PDz b i y)
    (RelCT.post (taintRel [.ebx, .ebp, .edx, .edi, .esp]
      (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [hx.ebx, hy.ebx, ei]
        · rw [hx.ebp, hy.ebp, ei']
        · rw [hx.edx, hy.edx, ei']
        · rw [hx.inv.edi, hy.inv.edi]; exact hq.cx.symm
        · exact hq.at_ hx.inv.at hy.inv.at) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (pd_ok ha hx) fun _ h => ⟨h.1, h.2.2⟩,
        WP.mono (pd_ok hb hy) fun _ h => ⟨h.1, h.2.2⟩⟩) ?_
  refine RelCT.seq (R := fun x y => Inv a x ∧ Inv b y)
    (RelCT.post (taintRel [.esi, .ecx, .edx, .edi, .esp]
      (fun x y ⟨⟨hx, _⟩, ⟨hy, _⟩⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [hx.esi, hy.esi, ei, ei']
        · rw [hx.ecx, hy.ecx, hq.c32]
        · rw [hx.edx, hy.edx, ei']
        · rw [hx.inv.edi, hy.inv.edi]; exact hq.cx.symm
        · exact hq.at_ hx.inv.at hy.inv.at) (by taint_decide))
      fun x y ⟨hx, hy⟩ =>
        ⟨WP.mono (copy_ok ha (by rw [hx.1.inv.rd]) (by rw [hx.1.inv.wr]) hsa.tail (by omega) (cp0 hx.1 hx.2))
          fun _ h => copied_inv ha hx.1 h,
         WP.mono (copy_ok hb (by rw [hy.1.inv.rd]) (by rw [hy.1.inv.wr]) hsb.tail (by omega) (cp0 hy.1 hy.2))
          fun _ h => copied_inv hb hy.1 h⟩) ?_
  exact absorbOne_rel ha hb hq (.inl rfl)

theorem macPad_rel {i : Nat} (hi : i = 1 ∨ i = 3) (hsa : Src a (arg a i) (arg a (i + 1)).toNat)
    (hsb : Src b (arg b i) (arg b (i + 1)).toNat) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) (macPad (4 + 4 * i) (8 + 4 * i)) fun _ _ => True := by
  have hi' : i + 1 < 5 := by omega
  have ei' : arg b (i + 1) = arg a (i + 1) := hq.args (i + 1) hi'
  rw [macPad_eq]
  refine RelCT.seq (R := fun x y => MA a i x ∧ MA b i y)
    (RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨WP.mono (maA_ok ha hi' hx) fun _ h => h.1,
      WP.mono (maA_ok hb hi' hy) fun _ h => h.1⟩) ?_
  · rcases hi with rfl | rfl <;>
    exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide)
  refine RelCT.seq (R := fun x y => MB a i x ∧ MB b i y)
    (RelCT.post (maB_rel ha hb hq hi' hsa hsb) fun x y ⟨hx, hy⟩ =>
      ⟨WP.mono (maB_ok ha hsa hx) fun _ h => h.1, WP.mono (maB_ok hb hsb hy) fun _ h => h.1⟩) ?_
  refine RelCT.seq (R := fun x y => MC a i x ∧ MC b i y)
    (RelCT.post (taintRel [.ebp, .edi, .esp]
      (fun x y ⟨hx, hy⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hx.ebp, hy.ebp, ei']
        · rw [hx.inv.edi, hy.inv.edi]; exact hq.cx.symm
        · exact hq.at_ hx.inv.at hy.inv.at) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (maC_ok hx) fun _ h => h.1, WP.mono (maC_ok hy) fun _ h => h.1⟩) ?_
  refine RelCT.ite (fun x y ⟨hx, hy⟩ => by simp only [eval, hx.zf, hy.zf, ei'])
    (relct_nil fun _ _ _ => trivial) fun x y t₁ t₂ x' y' ⟨⟨hx, hy⟩, he⟩ e₁ e₂ => ?_
  have h0 : (arg a (i + 1)).toNat % 16 ≠ 0 := by
    intro h0; simp [eval, hx.zf, h0] at he
  exact padTail_rel ha hb hq hsa hsb hi' h0 x y t₁ t₂ x' y' ⟨hx, hy⟩ e₁ e₂

theorem crypt_rel : RelCT isa (fun x y => Inv a x ∧ Inv b y) crypt fun _ _ => True := by
  rw [crypt_eq]
  exact RelCT.seq (R := fun x y => CrA a x ∧ CrA b y)
    (RelCT.post (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
      fun x y ⟨hx, hy⟩ => ⟨WP.mono (crA_ok ha hx) fun _ h => h.1, WP.mono (crA_ok hb hy) fun _ h => h.1⟩)
    (crB_rel ha hb hq)

theorem finalizeTo_rel {out : Nat} (ho : OutOk out) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) (finalizeTo out) fun _ _ => True := by
  rw [finalizeTo_eq]
  refine RelCT.seq (R := fun x y => FiA a out x ∧ FiA b out y)
    (RelCT.post ?_ fun x y ⟨hx, hy⟩ => ⟨WP.mono (fiA_ok hx out) fun _ h => h.1,
      WP.mono (fiA_ok hy out) fun _ h => h.1⟩) (fiB_rel ha hb hq ho)
  rcases ho with rfl | rfl <;>
  exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide)

/-! ## The functions -/

omit hq in
/-- A part that keeps the invariant. -/
theorem inv_rel {c : Prog isa} (h : RelCT isa (fun x y => Inv a x ∧ Inv b y) c fun _ _ => True)
    (hw : ∀ s₀ s, APre s₀ → Inv s₀ s → WP isa c s (Inv s₀)) :
    RelCT isa (fun x y => Inv a x ∧ Inv b y) c fun x y => Inv a x ∧ Inv b y :=
  RelCT.post h fun x y ⟨hx, hy⟩ => ⟨hw a x ha hx, hw b y hb hy⟩

theorem seal_rel : RelCT isa (fun x y => x = a ∧ y = b) «seal» fun _ _ => True := by
  rw [seal_eq]
  refine RelCT.seq (R := fun x y => Inv a x ∧ Inv b y) (RelCT.mono (prologue_rel ha hb hq) (fun _ _ h => h) fun x y ⟨hx, hy⟩ => ⟨hx.inv, hy.inv⟩) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inl rfl) (srcA ha) (srcA hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by omega) (srcA hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
    (fun s₀ _ hp h => WP.mono (lengths_ok hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (crypt_rel ha hb hq) (fun s₀ _ hp h => WP.mono (crypt_ok hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inr rfl) (srcD ha) (srcD hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by omega) (srcD hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (absorbOne_rel ha hb hq (.inr rfl))
    (fun s₀ _ hp h => WP.mono (absorbOne_ok hp h (.inr ⟨by omega, by omega⟩)) fun _ h => h.1)) ?_
  refine RelCT.seq (R := fun x y => Fin a x ∧ Fin b y) (RelCT.post (finalizeTo_rel ha hb hq (.inl rfl))
    fun x y ⟨hx, hy⟩ => ⟨WP.mono (finalizeTo_ok ha hx (.inl rfl)) fun _ h => h.1,
      WP.mono (finalizeTo_ok hb hy (.inl rfl)) fun _ h => h.1⟩) ?_
  exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.fin hx hy) (by taint_decide)

theorem open_rel : RelCT isa (fun x y => x = a ∧ y = b) «open» fun _ _ => True := by
  rw [open_eq]
  refine RelCT.seq (R := fun x y => Inv a x ∧ Inv b y) (RelCT.mono (prologue_rel ha hb hq) (fun _ _ h => h) fun x y ⟨hx, hy⟩ => ⟨hx.inv, hy.inv⟩) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inl rfl) (srcA ha) (srcA hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by omega) (srcA hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (macPad_rel ha hb hq (.inr rfl) (srcD ha) (srcD hb))
    (fun s₀ _ hp h => WP.mono (macPad_ok hp (by omega) (srcD hp) h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.inv hx hy) (by taint_decide))
    (fun s₀ _ hp h => WP.mono (lengths_ok hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (absorbOne_rel ha hb hq (.inr rfl))
    (fun s₀ _ hp h => WP.mono (absorbOne_ok hp h (.inr ⟨by omega, by omega⟩)) fun _ h => h.1)) ?_
  refine RelCT.seq (inv_rel ha hb (crypt_rel ha hb hq) (fun s₀ _ hp h => WP.mono (crypt_ok hp h) fun _ h => h.1)) ?_
  refine RelCT.seq (R := fun x y => Fin a x ∧ Fin b y) (RelCT.post (finalizeTo_rel ha hb hq (.inr rfl))
    fun x y ⟨hx, hy⟩ => ⟨WP.mono (finalizeTo_ok ha hx (.inr rfl)) fun _ h => h.1,
      WP.mono (finalizeTo_ok hb hy (.inr rfl)) fun _ h => h.1⟩) ?_
  exact taintRel [.edi, .esp] (fun x y ⟨hx, hy⟩ => hq.fin hx hy) (by taint_decide)

end

theorem seal_ct : ConstantTime isa sealX86.pre sealX86.pub «seal» :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (seal_rel (APre.of _ h₁) (APre.of _ h₂) (Pub.of hp) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ct : ConstantTime isa openX86.pre openX86.pub «open» :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (open_rel (APre.of _ h₁) (APre.of _ h₂) (Pub.of hp) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.ChaCha20Poly1305.X86
