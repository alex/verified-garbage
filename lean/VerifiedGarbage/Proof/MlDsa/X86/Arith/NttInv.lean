import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttSetup

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_inv_ntt`

The eight layers of Algorithm 42 (`nttInv_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the butterfly `ibflyBody` (`ibfly_spec`), with the negated
zetas from `zetas 255` down, then every coefficient times `8347681 = 256⁻¹ mod
q` (`scale_step`), by a Montgomery reduction of its product with `8347681` in
Montgomery form.
-/

namespace VG.Proof.MlDsa.X86.Arith.NttInvP

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ ldScratch layerCode layers blockInit blockEnd zDown)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Proof.MlDsa.X86.Arith.NttLoop
open VG.Spec.MlDsa (q n Poly Zq PolyIs Reduced coeffAt polyAt nttInvContract inPlaceContract inPlaceSig zetas)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_argAddr frameR retR Piece LeafPost satState wp_movm wp_mul ea_add
  ptr_next cnt_next cnt_ne toNat_ofNat32 eq_ofNat_of_toNat execMul_other)

/-- The butterfly of Algorithm 42. -/
def bf : Bfly := ⟨ibflyBody, bflyInv, ibfly_spec⟩

/-- The table entry of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 256 / len - 1 - c

/-- The zetas of Algorithm 42, negated. -/
def zv (k : Nat) : Zq := -zetas k

theorem tab : TabOK montNegZetaTable zv := fun _ hk => montNegZeta_eq hk

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : B + 1 ≤ 256 / len) (hk' : 256 / len ≤ 256)
    (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block ibflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zDown)) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ montNegZetaTable (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ montNegZetaTable (layerN bflyInv (P s₀) len (zf zv kf len) B) (kf len B) s)
      (layerCode ibflyBody zDown len) :=
  layer_piece bf montNegZetaTable zv kf P tab false len B hB hBp (fun c _ => by simp only [kf]; simp; omega)
    (fun c hc => by simp only [kf]; omega) (fun _ c hc => by simp only [kf]; omega) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

theorem nttInvLayer_eq (f : Poly) (len : Nat) :
    nttInvLayer f len = layerN bflyInv f len (zf zv kf len) (128 / len) := rfl

theorem fold_eq (f : Poly) : nttInvLens.foldl nttInvLayer f =
    nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer f 1)
      2) 4) 8) 16) 32) 64) 128 := by
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

theorem layers_piece : Piece Pre Pub (fun s₀ s => LB s₀ montNegZetaTable (F s₀) 255 s)
    (fun s₀ s => LB s₀ montNegZetaTable (nttInvLens.foldl nttInvLayer (F s₀)) 0 s)
    (layers (layerCode ibflyBody zDown) [1, 2, 4, 8, 16, 32, 64, 128]) := by
  refine Piece.seq (lay 1 128 (by decide) (by decide) (by decide) (by decide) F (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 2 64 (by decide) (by decide) (by decide) (by decide) (fun s₀ => nttInvLayer (F s₀) 1)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 4 32 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (F s₀) 1) 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 8 16 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 16 8 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4) 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 32 4 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4) 8) 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 64 2 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4) 8)
      16) 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 128 1 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1)
      2) 4) 8) 16) 32) 64)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [fold_eq]; exact h

/-! ## The scaling by `256⁻¹` -/

/-- The polynomial after the layers. -/
abbrev G (s₀ : State) : Poly := nttInvLens.foldl nttInvLayer (F s₀)

/-- `8347681`, the scaling factor, in `ℤ_q`. -/
abbrev c256 : Zq := 8347681

/-- After `k` coefficients are scaled. -/
structure SI (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] (P0 s₀).mem s.mem
  f : ∀ i < 256, (coeffAt s.mem (fA s₀) i).toNat = if i < k then ((G s₀)[i]! * c256).val else ((G s₀)[i]!).val

theorem scaleImm_toNat : scaleImm.toNat = (8347681 : Nat) * 2 ^ 32 % q := rfl

theorem scaleBody_eq : scaleBody =
    .mov .eax (.mem (at_ .esi 0)) :: .mov .edx (.imm scaleImm) :: .mul .edx :: (mred .ebx ++
      ([.store (at_ .esi 0) .ebx, .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)] : List Instr)) := by
  simp only [scaleBody, List.cons_append, List.nil_append]

theorem scale_step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 256) {s : State} (h : SI s₀ k s) :
    WP isa (.block scaleBody) s fun s' => SI s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (fA s₀) k := by
    rw [State.ea, at_, h.esi]; exact ea_ptr hp.f_fit hk
  have ha := h.f k hk
  rw [ite_eq_right (Nat.lt_irrefl k)] at ha
  have la := val_lt (G s₀)[k]!
  rw [scaleBody_eq]
  refine wp_movm (by rw [ef]; exact inRd (hp.in_f h.wr hk)) (wp_movi (wp_mul ?_))
  have hx : (8347681 * 2 ^ 32 % q) < q := Nat.mod_lt _ (by decide)
  have hlt : ((G s₀)[k]!).val * (8347681 * 2 ^ 32 % q) < q * 2 ^ 32 := by
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt la hx) (by decide)
  refine mred_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := ((G s₀)[k]!).val * (8347681 * 2 ^ 32 % q))
    ?_ hlt fun s₂ o₂ v₂ => ?_
  · rw [execMul_pair]
    simp only [State.setReg, ite_true, ite_false, reduceCtorEq]
    rw [ef, ← coeffAt_eq, ha, scaleImm_toNat]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3]), execMul_other _ _ h1 h2]
    simp only [State.setReg, h1, h2, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [o₂.mem]; rfl
  have rd₂ : s₂.rd = (P0 s₀).rd := by rw [o₂.rd]; exact h.rd
  have wr₂ : s₂.wr = (P0 s₀).wr := by rw [o₂.wr]; exact h.wr
  have hv : (s₂.gpr .ebx).toNat = ((G s₀)[k]! * c256).val := by
    rw [v₂, mont_mulR, val_mul]; rfl
  have out : InRegions s₂.wr (coeffAddr (fA s₀) k) 4 := hp.in_f wr₂ hk
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, esi₂, h.esi,
    ea_ptr hp.f_fit hk, out, ite_true,
    ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [g₂, h.esp], rd₂, wr₂, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide]
    exact ptr_next _ _ 4
  · simp only [ite_true, ecx₂, h.ecx]
    exact cnt_next hk
  · rw [m₂]; exact h.frame.writeW (by simp) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂]
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hv]
    · rw [ite_eq_right e, h.f i hi]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega)]
      · rw [ite_eq_right hik, ite_eq_right (by omega)]
  · simp only [eval, ecx₂, h.ecx]
    exact cnt_ne hk (by decide)

theorem scale_piece : Piece Pre Pub (fun s₀ s => LB s₀ montNegZetaTable (G s₀) 0 s) (SI · 256)
    (.seq (.block [.mov .esi (.mem (at_ .esp 20))]) (.seq (.block [.mov .ecx (.imm 256)])
      (.loop (.block scaleBody) .ne))) := by
  refine Piece.seq (B := fun s₀ s => LB s₀ montNegZetaTable (G s₀) 0 s ∧ s.gpr .esi = fP s₀) ?_ ?_
  · refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
    · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
        rw [h.esp]; exact P0_argAddr s₀ 0
      have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
        State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
      exact ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.ebp], h.mem⟩, by simp⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, pub_esp hq]
  refine Piece.seq (B := (SI · 0)) ?_ ?_
  · refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hsi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
      (by taint_decide)
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        Option.some.injEq, exists_eq_left']
      refine ⟨by simp [State.setReg, h.esp], h.rd, h.wr, by simp [State.setReg, hsi], by simp [State.setReg],
        h.mem.frame, fun i hi => ?_⟩
      rw [ite_eq_right (Nat.not_lt_zero i), show (s.setReg .ecx 256).mem = s.mem from rfl, polyIs_toNat h.mem.poly hi]
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, pub_esp hq]
  · exact Piece.countLoop (by decide) (fun k s₀ s => SI s₀ k s) [.esp, .esi, .ecx] (fun k hk s₀ s hp h => scale_step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.esp, h'.esp, pub_esp hq]
        · rw [h.esi, h'.esi, fP, fP, hq.2.1]
        · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (SI · 256)
    (.seq (.block ldScratch) (.seq (.block (nttSetup montNegZetaTable 255))
      (.seq (layers (layerCode ibflyBody zDown) [1, 2, 4, 8, 16, 32, 64, 128])
        (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
          (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne)))))) :=
  Piece.seq ld_piece (Piece.seq (setup_piece montNegZetaTable 255 (by taint_decide))
    (Piece.seq layers_piece scale_piece))

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (SI s₀ 256) s₀ s')
    Impl.MlDsa.X86.Arith.nttInv :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlDsa.X86.Arith.nttInv (nttInvContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlDsa.nttInv) h rfl) fun s s' _ _ h => by
      sig_pub [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm, nttInv_eq_layers]
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.f i hi, ite_eq_left hi, map_mul_get _ _ hi]
  · let st := satState satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlDsa.X86.Arith.NttInvP
