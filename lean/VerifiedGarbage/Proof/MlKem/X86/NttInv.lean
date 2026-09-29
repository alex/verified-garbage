import VerifiedGarbage.Proof.MlKem.X86.Ntt

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_inv_ntt`

Untrusted: everything here is checked by Lean. The seven layers of
Algorithm 10 (`nttInv_eq_layers`), each a `layer_piece` (`NttLoop.lean`)
of the inverse butterfly `ibflyBody` (`ibfly_spec`), with the zetas from
`zetas[127]` down; then every coefficient times 3303 (`scaleBody`).
-/

namespace VG.Proof.MlKem.X86.NttInvP

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.NttLoop
open VG.Proof.MlKem.X86.NttFwd (F nil_piece W hW)
open VG.Spec.MlKem

/-- The butterfly of Algorithm 10. -/
def bf : Bfly := ⟨ibflyBody, bflyInv, ibfly_spec⟩

/-- The zeta of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 256 / len - 1 - c

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 256 / len - 1 < 128)
    (hk1 : B + 1 ≤ 256 / len) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block ibflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zDown)) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ (layerN bflyInv kf (P s₀) len B) (kf len B) s) (layerCode ibflyBody zDown len) :=
  layer_piece bf kf P false len B hB hBp (fun c _ => by simp only [kf, Bool.false_eq_true, ite_false]; omega)
    (fun c hc => by simp only [kf]; omega) (fun _ c hc => by simp only [kf]; omega) t₁ t₂ t₃ t₄

theorem nttInvLayer_eq (f : Poly) (len : Nat) :
    nttInvLayer f len = layerN bflyInv kf f len (128 / len) := rfl

theorem fold_eq (f : Poly) : nttInvLens.foldl nttInvLayer f =
    layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf
      (layerN bflyInv kf (layerN bflyInv kf f 2 64) 4 32) 8 16) 16 8) 32 4) 64 2) 128 1 := by
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil, nttInvLayer_eq, Nat.reduceDiv]

theorem layers_piece : Piece Pre Pub (fun s₀ s => LB s₀ (F s₀) 127 s)
    (fun s₀ s => LB s₀ (nttInvLens.foldl nttInvLayer (F s₀)) 0 s)
    (layers (layerCode ibflyBody zDown) [2, 4, 8, 16, 32, 64, 128]) := by
  refine Piece.seq (lay 2 64 (by decide) (by decide) (by decide) (by decide) F (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 4 32 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv kf (F s₀) 2 64)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 8 16 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv kf (layerN bflyInv kf (F s₀) 2 64) 4 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 16 8 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (F s₀) 2 64) 4 32) 8 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 32 4 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (F s₀) 2 64)
      4 32) 8 16) 16 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 64 2 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf
      (layerN bflyInv kf (F s₀) 2 64) 4 32) 8 16) 16 8) 32 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (lay 128 1 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf (layerN bflyInv kf
      (layerN bflyInv kf (layerN bflyInv kf (F s₀) 2 64) 4 32) 8 16) 16 8) 32 4) 64 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [fold_eq]; exact h

/-! ## The multiplication by 3303 -/

/-- `G` with its first `t` coefficients times 3303. -/
def scaled (G : Poly) (t : Nat) : Poly := Vector.ofFn fun i => if i.val < t then G[i.val]! * 3303 else G[i.val]!

theorem scaled_get (G : Poly) (t : Nat) {i : Nat} (hi : i < n) :
    (scaled G t)[i]! = if i < t then G[i]! * 3303 else G[i]! := by
  rw [getElem!_eq _ hi, scaled, Vector.getElem_ofFn]

theorem scaled_zero (G : Poly) : scaled G 0 = G :=
  ext_getElem! fun i hi => by rw [scaled_get _ _ hi, ite_eq_right (Nat.not_lt_zero i)]

theorem scaled_succ (G : Poly) (t : Nat) :
    scaled G (t + 1) = (scaled G t).set! t (G[t]! * 3303) :=
  ext_getElem! fun i hi => by
    rw [scaled_get _ _ hi]
    by_cases e : t = i
    · subst e; rw [getElem!_set!_self _ hi, ite_eq_left (by omega)]
    · rw [getElem!_set!_ne _ hi e, scaled_get _ _ hi]
      by_cases h : i < t
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]

theorem scaled_all (G : Poly) : scaled G 256 = G.map (· * 3303) :=
  ext_getElem! fun i hi => by rw [scaled_get _ _ hi, ite_eq_left (by rw [n_eq] at hi; exact hi), map_mul_get _ hi]

/-- After `t` coefficients. -/
structure SI (s₀ : State) (G : Poly) (t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * t)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - t)
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] (P0 s₀).mem s.mem
  poly : PolyIs s.mem (fA s₀) (scaled G t)

theorem scale_step {s₀ : State} (hp : Pre s₀) {G : Poly} {t : Nat} (ht : t < 256) {s : State}
    (h : SI s₀ G t s) :
    WP isa (.block scaleBody) s fun s' => SI s₀ G (t + 1) s' ∧ eval .ne s' = some (decide (t + 1 < 256)) := by
  have ff := hp.f_fit
  have ht' : t < n := by rw [n_eq]; exact ht
  have ea : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (fA s₀) t := by
    rw [h.esi, ea_add (by omega), Nat.add_zero]
  have inF := hp.in_f h.wr ht
  have ha := polyIs_coeffAt h.poly ht'
  rw [coeffAt_eq] at ha
  have la := val_lt (scaled G t)[t]!
  generalize ea' : (scaled G t)[t]!.val = a at ha la
  have ha' : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  rw [scaleBody]
  refine wp_movm (by rw [State.ea, at_, ea]; exact inRd inF) (wp_cons rfl (wp_mul (wp_movr
    (red_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := a * 3303) ?_ ?_ fun s₂ o₂ v₂ => ?_))))
  · simp only [State.setReg, execMul_eax, ite_true, ite_false, State.ea, at_, ea, ha, reduceCtorEq]
    simp only [ha', show (3303 : BitVec 32).toNat = 3303 from rfl]
    exact toNat_ofNat32 (by omega)
  · simp only [State.setReg, execMul_eax, ite_true, ite_false, State.ea, at_, ea, ha, reduceCtorEq]
    simp only [ha', show (3303 : BitVec 32).toNat = 3303 from rfl]
    exact toNat_ofNat32 (by omega)
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3])]
    simp only [State.setReg, h3, ite_false]
    rw [execMul_other _ _ h1 h2]
    simp only [h1, h2, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have esp₂ := g₂ .esp (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := o₂.mem
  have wr₂ : s₂.wr = s.wr := o₂.wr
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 (a * 3303 % q) := eq_ofNat_of_toNat v₂
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₂, ecx₂, m₂, wr₂, bx₂, ea, inF, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  have hv : BitVec.ofNat 32 (a * 3303 % q) = BitVec.ofNat 32 ((G[t]! * 3303).val) := by
    rw [← ea', scaled_get _ _ ht', ite_eq_right (Nat.lt_irrefl t), val_mul]
    rfl
  refine ⟨⟨by simp [esp₂, h.esp], o₂.rd.trans h.rd, h.wr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [show Reg.esi ≠ Reg.ecx by decide, ite_false, ite_true, h.esi]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next ht
  · exact h.frame.writeW (by simp) _ (coeff_contains _ ht')
  · rw [hv, scaled_succ]
    exact polyIs_writeW h.poly ht' _
  · simp only [eval, h.ecx]
    exact cnt_ne ht (by omega)

/-- The polynomial after the layers. -/
abbrev G (s₀ : State) : Poly := nttInvLens.foldl nttInvLayer (F s₀)

/-- `esi` at `f`, the layers done. -/
structure SA (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] (P0 s₀).mem s.mem
  poly : PolyIs s.mem (fA s₀) (G s₀)

theorem esi_piece : Piece Pre Pub (fun s₀ s => LB s₀ (G s₀) 0 s) SA (.block [.mov .esi (.mem (at_ .esp 20))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
      rw [h.esp]; exact P0_argAddr s₀ 0
    have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
      State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨by simp [h.esp], h.rd, h.wr, by simp, h.mem.frame, h.mem.poly⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, pub_esp hq]

theorem ecx_piece : Piece Pre Pub SA (fun s₀ s => SI s₀ (G s₀) 0 s) (.block [.mov .ecx (.imm 256)]) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
    Option.some.injEq, exists_eq_left']
  exact ⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], by simp, h.frame, by rw [scaled_zero]; exact h.poly⟩

theorem scale_piece : Piece Pre Pub (fun s₀ s => SI s₀ (G s₀) 0 s) (fun s₀ s => SI s₀ (G s₀) 256 s)
    (.loop (.block scaleBody) .ne) :=
  Piece.countLoop (by decide) (fun t s₀ s => SI s₀ (G s₀) t s) [.esp, .esi, .ecx]
    (fun t ht s₀ s hp h => scale_step hp ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.esp, h'.esp, pub_esp hq]
      · rw [h.esi, h'.esi, fP, fP, hq.2.1]
      · rw [h.ecx, h'.ecx]) (by taint_decide)

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (fun s₀ s => SI s₀ (G s₀) 256 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup 127))
      (.seq (layers (layerCode ibflyBody zDown) [2, 4, 8, 16, 32, 64, 128])
        (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
          (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne)))))) :=
  Piece.seq ld_piece (Piece.seq (setup_piece 127 (by taint_decide)) (Piece.seq layers_piece
    (Piece.seq esi_piece (Piece.seq ecx_piece scale_piece))))

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => SI s₀ (G s₀) 256 s) s₀ s') Impl.MlKem.X86.nttInv :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlKem.X86.nttInv (nttInvContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlKem.nttInv) h rfl)
      fun s s' _ _ h => by
        sig_pub [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] at h
        exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    rw [hm, nttInv_eq_layers, ← scaled_all]
    exact hinv.poly
  · let st := satState NttFwd.satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
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
           simp only [NttFwd.satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlKem.X86.NttInvP
