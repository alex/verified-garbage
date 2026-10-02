import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.Sample.Word
import VerifiedGarbage.Impl.MlDsa.X86.Sample.ExpandMask

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_expand_mask_poly`

The body is the SHAKE256 output of the seed at `scratch + 840`
(`sponge_piece`), then a branch on the public `γ₁` to the loop for its width
`c` (18 or 20), whose iteration `g` stores coefficients `4g` to `4g + 3`
(`coef_ok`): coefficient `i` reads the 32-bit word at byte `⌊ci/8⌋` of the
output, whose bits from `ci mod 8` on are those of the output from bit `ci` on
(`wordBits`: only its first 3 bytes matter), and stores `γ₁` minus their low
`c` bits modulo `q` (`subMask_eq`). Every address and branch depends only on
the pointers and `γ₁`: the taint analysis proves it constant time.
-/

namespace VG.Proof.MlDsa.X86.Sample.ExpandMask

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.X86.Sample (argOp emCoef emBody emLoop qImm sponge)
open VG.Spec.MlDsa (Zq q H n ofInt coeffAt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86.Sample (cR E1)
open VG.Proof.MlDsa.X86.Sample.RejNtt (nil_piece)

/-- The layout: `expandMask(seed, gamma1, a, scratch)`, 66 bytes of seed,
640 bytes of SHAKE256. -/
def L : Lay := { nA := 4, iA := 2, iS := 3, rate := 136, outlen := 640, mlen := some 66 }

theorem hL : L.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun k hk => by cases hk; decide,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- `γ₁`. -/
abbrev γ (s₀ : State) : Nat := (arg s₀ 1).toNat

/-- The precondition. -/
def EPre (s₀ : State) : Prop := Pre L s₀ ∧ (γ s₀ = 2 ^ 17 ∨ γ s₀ = 2 ^ 19)

/-- The XOF output. -/
abbrev X (s₀ : State) : List Byte := L.out s₀

/-- The value stored for coefficient `i` of `c` bits of the output `X`. -/
abbrev emV (X : List Byte) (c i : Nat) : BitVec 32 :=
  zw (ofInt (((2 ^ (c - 1) : Nat) : Int) - (leNat X / 2 ^ (i * c) % 2 ^ c : Nat)))

/-- The widths of the coefficients. -/
def emOk (c : Nat) : Prop := c = 18 ∨ c = 20

/-! ## The loop -/

/-- Group `g`, with its first `k` coefficients stored. -/
structure GInv (c : Nat) (s₀ : State) (g k : Nat) (s : State) : Prop extends Base L s₀ s where
  out : ∀ p < 640, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (X s₀).getD p 0
  esi : s.gpr .esi = L.sP s₀ + BitVec.ofNat 32 (840 + c / 2 * g)
  edi : s.gpr .edi = L.aP s₀ + BitVec.ofNat 32 (16 * g)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (64 - g)
  coef : ∀ i < 4 * g + k, coeffAt s.mem (L.aA s₀) i = emV (X s₀) c i
  cγ : c = emC (γ s₀)

theorem emOk_le {c : Nat} (hc : emOk c) : c / 2 * 63 + c * 3 / 8 ≤ 637 := by rcases hc with rfl | rfl <;> decide

/-- Coefficient `4g + k`. -/
theorem coef_ok {c : Nat} (hc : emOk c) {s₀ : State} (hp : Pre L s₀) {g k : Nat} (hg : g < 64) (hk : k < 4)
    {s : State} (h : GInv c s₀ g k s) : WP isa (.block (emCoef c k)) s (GInv c s₀ g (k + 1)) := by
  have hs := hp.s_fit
  have ha := hp.a_fit
  have hle := emOk_le hc
  have hkk : c * k / 8 ≤ c * 3 / 8 := Nat.div_le_div_right (Nat.mul_le_mul_left c (by omega))
  have hg' : c / 2 * g ≤ c / 2 * 63 := Nat.mul_le_mul_left _ (by omega)
  have hc' : c ≤ 20 := by rcases hc with rfl | rfl <;> omega
  have hsh : c * k % 8 + c ≤ 24 := by rcases hc with rfl | rfl <;> omega
  -- the word read
  have eld : (L.sP s₀ + BitVec.ofNat 32 (840 + c / 2 * g) + BitVec.ofNat 32 (c * k / 8)).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (840 + (c / 2 * g + c * k / 8)) := by
    rw [ea_add (by simp only [L] at hs ⊢; omega), Nat.add_assoc]
  have ild := hp.inS' h.wr (o := 840 + (c / 2 * g + c * k / 8)) (n := 4) (by omega)
  -- the coefficient stored
  have est : (L.aP s₀ + BitVec.ofNat 32 (16 * g) + BitVec.ofNat 32 (4 * k)).setWidth 64 =
      coeffAddr (L.aA s₀) (4 * g + k) := by
    rw [ea_add (by simp only [L] at ha ⊢; omega)]; congr 2; omega
  have ist : InRegions s.wr (coeffAddr (L.aA s₀) (4 * g + k)) 4 := hp.inA h.wr (by omega)
  -- its value
  generalize hw : s.mem.readW (L.sA s₀ + BitVec.ofNat 64 (840 + (c / 2 * g + c * k / 8))) 32 = w
  have hx : (w >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)).toNat =
      leNat (X s₀) / 2 ^ ((4 * g + k) * c) % 2 ^ c := by
    rw [BitVec.toNat_and, toNat_shr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 ^ c - 1) (by
      have : 2 ^ c ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hc'; omega), Nat.and_two_pow_sub_one_eq_mod,
      ← hw, wordBits s.mem _ (X s₀) (o := c / 2 * g + c * k / 8) hsh fun b hb => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
        exact h.out (c / 2 * g + c * k / 8 + b) (by omega),
      show 8 * (c / 2 * g + c * k / 8) + c * k % 8 = (4 * g + k) * c by rcases hc with rfl | rfl <;> omega]
  have e2 : (BitVec.ofNat 32 (2 ^ (c - 1))).toNat = 2 ^ (c - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have : 2 ^ (c - 1) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega); omega)]
  have hv : BitVec.ofNat 32 (2 ^ (c - 1)) - (w >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)) +
      ((w >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)) - (w >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)) -
        (BitVec.ofBool (decide ((BitVec.ofNat 32 (2 ^ (c - 1))).toNat <
          (w >>> (c * k % 8) &&& BitVec.ofNat 32 (2 ^ c - 1)).toNat))).setWidth 32 &&& qImm) =
      emV (X s₀) c (4 * g + k) := by
    refine (subMask_eq (by rw [e2]; rcases hc with rfl | rfl <;> decide) (by
      rw [hx, e2]; have := Nat.mod_lt (leNat (X s₀) / 2 ^ ((4 * g + k) * c)) (Nat.two_pow_pos c)
      have : 2 ^ (c - 1) < q := by rcases hc with rfl | rfl <;> decide
      have : 2 ^ c = 2 * 2 ^ (c - 1) := by rcases hc with rfl | rfl <;> rfl
      omega)).trans ?_
    rw [hx, e2]
  have fa : ∀ v : BitVec 32, Frame [L.aR s₀] s.mem (s.mem.writeW (coeffAddr (L.aA s₀) (4 * g + k)) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ (by omega))
  have fin : ∀ s' : State, s'.gpr .esp = s.gpr .esp → s'.gpr .esi = s.gpr .esi → s'.gpr .edi = s.gpr .edi →
      s'.gpr .ecx = s.gpr .ecx → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW (coeffAddr (L.aA s₀) (4 * g + k)) (emV (X s₀) c (4 * g + k)) →
      GInv c s₀ g (k + 1) s' := by
    intro s' e1 e2 e3 e4 e5 e6 e7
    refine ⟨⟨by rw [e1, h.esp], by rw [e5, h.rd], by rw [e6, h.wr], ?_⟩, fun p hp' => ?_, by rw [e2, h.esi],
      by rw [e3, h.edi], by rw [e4, h.ecx], fun i hi => ?_, h.cγ⟩
    · rw [e7]; exact h.frame.writeW (r := L.aR s₀) (by simp) _ (coeff_contains _ (by omega))
    · rw [e7]
      refine ((fa _) _ fun r hr hc => ?_).trans (h.out p hp')
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s _ hc ((hp.sub_s (o := 840 + p) (n := 1) (by omega)) _ (Region.contains_self _ _))
    · rw [e7, coeffAt_writeW _ _ (by omega) (by omega)]
      by_cases e : 4 * g + k = i
      · rw [ifT e, ← e]
      · rw [ifF e]; exact h.coef i (by omega)
  apply WP.of_runBlock
  by_cases hs0 : c * k % 8 = 0
  · rw [hs0, BitVec.ushiftRight_zero] at hv
    simp (config := {decide := true}) only [emCoef, hs0, ite_true, List.nil_append, List.cons_append,
      at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32,
      State.store32, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, h.esi, h.edi,
      eld, ild, est, ist, hw, hv, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact fin _ (by simp) (by simp) (by simp) (by simp) rfl rfl rfl
  · have h1 : 1 ≤ c * k % 8 := by omega
    have h2 : c * k % 8 ≤ 31 := by omega
    simp (config := {decide := true}) only [emCoef, hs0, ite_false, List.nil_append, List.cons_append,
      at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc, State.ea, State.load32,
      State.store32, State.setReg, arithFlags, State.setFlags, Option.map_some, Option.bind_some, h.esi, h.edi,
      eld, ild, est, ist, hw, hv, h1, h2, and_self, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    exact fin _ (by simp) (by simp) (by simp) (by simp) rfl rfl rfl

/-- A group of 4 coefficients, and the pointers and counter advanced. -/
theorem body_ok {c : Nat} (hc : emOk c) {s₀ : State} (hp : Pre L s₀) {g : Nat} (hg : g < 64)
    {s : State} (h : GInv c s₀ g 0 s) :
    WP isa (.block (emBody c)) s fun s' => GInv c s₀ (g + 1) 0 s' ∧ eval .ne s' = some (decide (g + 1 < 64)) := by
  rw [emBody, show (List.range 4).flatMap (emCoef c) =
      emCoef c 0 ++ (emCoef c 1 ++ (emCoef c 2 ++ (emCoef c 3 ++ []))) from rfl, List.append_nil,
    List.append_assoc, WP.block_append_iff]
  refine (coef_ok hc hp hg (by omega) h).mono fun s1 h1 => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine (coef_ok hc hp hg (by omega) h1).mono fun s2 h2 => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine (coef_ok hc hp hg (by omega) h2).mono fun s3 h3 => ?_
  rw [WP.block_append_iff]
  refine (coef_ok hc hp hg (by omega) h3).mono fun h4s h4 => ?_
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', ↓reduceIte]
  refine ⟨⟨⟨by simp [h4.esp], h4.rd, h4.wr, h4.frame⟩, h4.out, ?_, ?_, ?_,
    fun i (hi : i < 4 * (g + 1) + 0) => h4.coef i (by omega), h4.cγ⟩, ?_⟩
  · simp (config := {decide := true}) only [↓reduceIte, h4.esi]
    rw [add_ofNat_add, show 840 + c / 2 * g + c / 2 = 840 + c / 2 * (g + 1) by rw [Nat.mul_succ]; omega]
  · simp (config := {decide := true}) only [↓reduceIte, h4.edi]
    rw [show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_add]; congr 2
  · simp (config := {decide := true}) only [↓reduceIte, h4.ecx]
    exact cnt_next hg
  · simp only [eval, h4.ecx]
    exact cnt_ne hg (by omega)

theorem loop_piece {c : Nat} (hc : emOk c)
    (ht : TaintOk [.esi, .edi] (.block (emBody c))) :
    Piece EPre (PubP L) (fun s₀ s => GInv c s₀ 0 0 s) (fun s₀ s => GInv c s₀ 64 0 s)
      (.loop (.block (emBody c)) .ne) := by
  obtain ⟨_, ht⟩ := ht
  exact Piece.countLoop (by decide) (fun g s₀ s => GInv c s₀ g 0 s) [.esi, .edi]
    (fun g hg s₀ s hp h => body_ok hc hp.1 hg h)
    (fun g _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.esi, h'.esi, hq.sP hL]
      · rw [h.edi, h'.edi, hq.aP hL]) ht

/-- Before the branch on `γ₁`: `edi = a`, and whether `γ₁ = 2¹⁷` in ZF. -/
def Sel (s₀ s : State) : Prop :=
  Out L s₀ s ∧ s.gpr .edi = L.aP s₀ ∧ eval .e s = some (decide (γ s₀ = 2 ^ 17))

theorem sel_piece : Piece EPre (PubP L) (Out L) Sel
    (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 0x20000)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp.1 (i := 1) (by decide)
    have v₁ := h.args 1 (by decide)
    have a₂ := h.argEa (i := 2)
    have i₂ := h.argIn hp.1 (i := 2) (by decide)
    have v₂ := h.args 2 (by decide)
    simp only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at a₁ a₂
    apply WP.of_runBlock
    simp (config := {decide := true}) only [argOp, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags, Option.map_some,
      Option.bind_some, a₁, i₁, v₁, a₂, i₂, v₂, ite_true, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.out⟩, by simp; rfl, ?_⟩
    simp only [eval, sub_beq_zero]
    rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.e1]

theorem init_piece (c : Nat) (b : Bool) (hb : ∀ s₀, decide (γ s₀ = 2 ^ 17) = b → c = emC (γ s₀)) :
    Piece EPre (PubP L) (fun s₀ s => Sel s₀ s ∧ decide (γ s₀ = 2 ^ 17) = b) (fun s₀ s => GInv c s₀ 0 0 s)
    (.block [.alu .add .esi (.imm (BitVec.ofNat 32 840)), .mov .ecx (.imm 64)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨h, hdi, _⟩, e⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [hdi], by simp,
    fun i hi => absurd hi (by omega), hb s₀ e⟩

/-- The end: the polynomial of `ExpandMask` at `a`. -/
def Fin (s₀ s : State) : Prop :=
  Base L s₀ s ∧ Spec.MlDsa.PolyIs s.mem (L.aA s₀)
    (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack (H (L.Msg s₀) (32 * (1 + Spec.MlDsa.bitlen (γ s₀ - 1))))
      (γ s₀ - 1) (γ s₀)))

theorem fin_of {c : Nat} {s₀ s : State} (hγ : γ s₀ = 2 ^ 17 ∨ γ s₀ = 2 ^ 19) (hc : c = emC (γ s₀))
    (h : GInv c s₀ 64 0 s) : Fin s₀ s := by
  refine ⟨h.toBase, polyIs_of_coeffAt fun i hi => ?_⟩
  rw [expandMask_getElem _ hγ hi, h.coef i (by simp only [n] at hi; omega), emV, ← hc, (emC_eq hγ).2.2]
  have : X s₀ = H (L.Msg s₀) 640 := (H_eq _ _).symm
  rw [this, show 2 ^ (emC (γ s₀) - 1) = 2 ^ (c - 1) by rw [hc]]

theorem branch_piece : Piece EPre (PubP L) Sel Fin (.ite .e (emLoop 18) (emLoop 20)) := by
  refine Piece.ite (fun s₀ => decide (γ s₀ = 2 ^ 17)) (fun _ _ _ h => h.2.2)
    (fun s₀ s₀' _ _ hq => by rw [γ, γ, hq.2 1 (by decide)]) ?_ ?_
  · refine (Piece.seq (init_piece 18 true fun s₀ e => by rw [emC, ifT (of_decide_eq_true e)])
      (loop_piece (Or.inl rfl) ⟨_, by taint_decide⟩)).mono (fun _ _ _ h => h) fun s₀ s hp h => ?_
    exact fin_of hp.2 h.cγ h
  · refine (Piece.seq (init_piece 20 false fun s₀ e => by rw [emC, ifF (of_decide_eq_false e)])
      (loop_piece (Or.inr rfl) ⟨_, by taint_decide⟩)).mono (fun _ _ _ h => h) fun s₀ s hp h => ?_
    exact fin_of hp.2 h.cγ h

end VG.Proof.MlDsa.X86.Sample.ExpandMask

namespace VG.Proof.MlDsa.X86.Sample.ExpandMask

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlDsa.X86.Sample
open VG.Impl.MlDsa.X86.Sample (argOp emLoop sponge)

/-! ## The whole function -/

theorem main_piece : Piece EPre (PubP L) (fun s₀ s => s = P0 s₀) Fin
    (.seq (sponge 3 136 (.imm 66) 640)
      (.seq (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 0x20000)])
        (.ite .e (emLoop 18) (emLoop 20)))) :=
  Piece.seq ((sponge_piece hL).pre_mono (fun _ h => h.1) fun _ _ _ _ h => h) <|
    Piece.seq sel_piece branch_piece

theorem piece : Piece EPre (PubP L) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlDsa.X86.Sample.expandMask :=
  Piece.leaf L.W (NoSp.of_all (by decide +kernel))
    (fun _ hp => ⟨by have := hp.1.sp; omega, by have := hp.1.sp'; omega⟩)
    (fun _ hp => hp.1.hW) (fun _ _ _ _ hq => hq.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩)

theorem EPre.of {s₀ : State} (h : (Spec.MlDsa.expandMaskContract X86.abi 56).pre s₀) : EPre s₀ := by
  sig_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    show (66 : Nat) < 136 by decide⟩, h22⟩

/-- Memory with the arguments `0`, `2¹⁷`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x500a then 2 else if a = 0x500d then 1 else if a = 0x5011 then 0x10 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Sample.expandMask (Spec.MlDsa.expandMaskContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => EPre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h
    refine ⟨e₁, fun i hi => ?_⟩
    match i, hi with
    | 0, _ => exact e₂
    | 1, _ => exact e₃
    | 2, _ => exact e₄
    | 3, _ => exact e₅
  · obtain ⟨habi, -, -, s, ⟨-, hf⟩, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [hm]
    exact hf
  · let st := satState satMem [⟨0, 66⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]

end VG.Proof.MlDsa.X86.Sample.ExpandMask
