import VerifiedGarbage.Proof.MlDsa.X86.Sample.Setup

/-!
# ML-DSA on x86 (32-bit): the SHAKE output of the sampling functions

Untrusted: everything here is checked by Lean. `sponge` (the start of each
sampling function, `Impl/MlDsa/X86/Sample/Common.lean`) loads `scratch`
into `esi` (`ld_piece`), zeroes the Keccak state at `scratch` (`zero_piece`),
absorbs the message, pads it, and squeezes `outlen` bytes to
`scratch + 840` with the verified Keccak functions (`absorb_call`,
`pad_call`, `squeeze_call`), leaving the first `outlen` bytes of the XOF
output of the message there (`Out`), for any layout `L` (`sponge_piece`).
The calls are those of ML-KEM (`Proof/MlKem/X86/Keccak.lean`), but for a
message length and a padding position that depend on the entry state
(`absorb_piece'`, `pad_piece'`).
-/

namespace VG.Proof.MlDsa.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr squeezeFrom shakeSuffix absorb pad rates)
open VG.Proof.MlKem.X86.Sample (cR E1 stateAt_zero zero_write toNat_off)
open VG.Impl.MlDsa.X86.Sample (argOp absArgs padArgs sqzArgs sponge)
open VG.Proof.MlKem (repr_nil shakeSuffix32 bytesAt_getD bytesAt_length)

/-! ## The Keccak calls, for lengths that depend on the entry state -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop}

/-- A call of `vg_keccak_absorb`, from position 0, of `len s₀` bytes. -/
theorem absorb_piece' (E S D W : State → BitVec 32) (rate : Nat) (len : State → Nat) (hr : rate ∈ rates)
    (hlen : ∀ s₀, Pre s₀ → len s₀ < 2 ^ 32)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → AbsorbAt s (E s₀) (S s₀) (D s₀) (W s₀) rate 0 (len s₀))
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ D s₀ = D s₀' ∧ W s₀ = W s₀' ∧ len s₀ = len s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → 0 = msg.length % rate →
        Repr s'.mem ((S s₀).setWidth 64) rate (msg ++ bytesAt s.mem ((D s₀).setWidth 64) (len s₀))) →
      B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs6 "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) := by
  have hp0 : 0 < rate := by simp [rates] at hr; omega
  refine Piece.callWith Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 absorb_nosp (by decide) (by decide)
    (fun s₀ => [reg32 (D s₀) (len s₀)]) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 24])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [absorb_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact absorb_pre h.esp h.args h.bufs h.fD h.dDS h.dDW h.bD hr hp0 (hlen s₀ h₀) h.cD h.cS h.cW
  · obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄, ← e₅] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨by rw [e₃, e₅], by rw [e₁, e₂, e₄], hsp,
      args6_eq (by rw [h.esp]; exact h.bufs.hE) hsp (absArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (absorb_post h.esp h.args hE (hlen s₀ h₀) (rate_lt hr) (by have := rate_lt hr; omega) h.bufs.bS h.bD post)
    rw [absorb_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

/-- A call of `vg_keccak_pad`, from position `pos s₀`. -/
theorem pad_piece' (E S W : State → BitVec 32) (rate : Nat) (pos : State → Nat) (sfx : Nat) (hr : rate ∈ rates)
    (hp : ∀ s₀, Pre s₀ → pos s₀ < rate)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → PadAt s (E s₀) (S s₀) (W s₀) rate (pos s₀) sfx)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ W s₀ = W s₀' ∧ pos s₀ = pos s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → pos s₀ = msg.length % rate →
        stateAt s'.mem ((S s₀).setWidth 64) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) →
      B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith rs5 "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 pad_nosp (by decide) (by decide)
    (fun _ => []) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 20])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [pad_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact pad_pre h.esp h.args h.bufs hr (hp s₀ h₀) h.cS h.cW
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨rfl, by rw [e₁, e₂, e₃], hsp,
      args5_eq (by rw [h.esp]; exact h.bufs.hE) hsp (padArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (pad_post h.esp h.args hE (rate_lt hr) (by have := rate_lt hr; have := hp s₀ h₀; omega) h.bufs.bS post)
    rw [pad_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

end

variable {L : Lay}

/-! ## `esi = scratch` -/

theorem ld_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (fun s₀ s => s = P0 s₀) (Ctx L)
    (.block [.mov .esi (.mem (argOp L.iS))]) := by
  obtain ⟨_, ht⟩ := hL.tLd
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) ht
  · subst e
    have b₀ : Base L s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a₂ := b₀.argEa (i := L.iS)
    have i₂ := b₀.argIn hp hL.iS
    have v₂ := args0 hp L.iS hL.iS
    apply WP.of_runBlock
    simp only [argOp, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₂, i₂, v₂, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨⟨by simp, rfl, rfl, Frame.refl _ _⟩, fun i hi => by simpa using args0 hp i hi, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]


/-- The arguments are intact after changes to memory only within regions
apart from them. -/
theorem args_frame {s₀ : State} (hp : Pre L s₀) {m m' : Mem}
    (h : ∀ i < L.nA, m.readW (argAddr s₀ i) 32 = arg s₀ i) {rs : List Region} (fr : Frame rs m m')
    (hd : ∀ r ∈ rs, (L.gR s₀).Disjoint r) : ∀ i < L.nA, m'.readW (argAddr s₀ i) 32 = arg s₀ i :=
  fun i hi => by rw [fr.readW (arg_contains hi hp.sp') hd (by decide)]; exact h i hi

/-! ## The Keccak state set to zero -/

/-- After `k` words. -/
structure ZInv (L : Lay) (s₀ : State) (k : Nat) (s : State) : Prop extends Ctx L s₀ s where
  ebx : s.gpr .ebx = L.sP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (50 - k)
  eax : s.gpr .eax = 0
  zero : ∀ j < 4 * k, s.mem (L.sA s₀ + BitVec.ofNat 64 j) = 0

theorem zinit_piece : Piece (Pre L) (PubP L) (Ctx L) (ZInv L · 0) (.block (zeroInit 0)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [zeroInit, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq,
    exists_eq_left']
  exact ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, by simp [h.esi], by simp, by simp,
    fun j hj => absurd hj (by omega)⟩

theorem zstep {s₀ : State} (hp : Pre L s₀) {k : Nat} (hk : k < 50) {s : State} (h : ZInv L s₀ k s) :
    WP isa (.block zeroBody) s fun s' => ZInv L s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 50)) := by
  have hs := hp.s_fit
  have ea : (L.sP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 =
      L.sA s₀ + BitVec.ofNat 64 (4 * k) := by
    rw [ea_add (by omega)]; rfl
  have hin : InRegions s.wr (L.sA s₀ + BitVec.ofNat 64 (4 * k)) 4 := hp.inS h.wr (by omega)
  have fr : Frame [L.sR s₀] s.mem (s.mem.writeW (L.sA s₀ + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_at (by omega) hs)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [zeroBody, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, h.ebx, ea, hin, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, ?_⟩, ?_, by simp [h.esi]⟩, ?_, ?_, by simp [h.eax], ?_⟩, ?_⟩
  · exact h.frame.writeW (r := L.sR s₀) (by simp) _ (contains_at (by omega) hs)
  · rw [h.eax]
    exact args_frame hp h.args fr (by simp only [List.mem_singleton, forall_eq]; exact hp.s_g.symm)
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [h.eax]; exact zero_write h.zero
  · simp only [eval, h.ecx]
    exact cnt_ne hk (by omega)

theorem zloop_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (ZInv L · 0) (ZInv L · 50) (.loop (.block zeroBody) .ne) :=
  Piece.countLoop (by decide) (fun k s₀ s => ZInv L s₀ k s) [.ebx]
    (fun k hk s₀ s hp h => zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ebx, h'.ebx, hq.sP hL]) (by taint_decide)

/-- `Ctx`, with the Keccak state zero. -/
structure Z (L : Lay) (s₀ s : State) : Prop extends Ctx L s₀ s where
  st : stateAt s.mem (L.sA s₀) = Spec.Sha3.zero

theorem zero_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (Ctx L) (Z L) (zeroSt 0) :=
  (Piece.seq zinit_piece (zloop_piece hL)).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨h.toCtx, stateAt_zero fun j hj => h.zero j (by omega)⟩


/-! ## Absorbing the message -/

theorem ml_ofNat {s₀ : State} : BitVec.ofNat 32 (L.ml s₀) =
    match L.mlen with | some k => BitVec.ofNat 32 k | none => arg s₀ 1 := by
  unfold Lay.ml; cases h : L.mlen <;> simp

theorem absArgs_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (Z L)
    (fun s₀ s => Z L s₀ s ∧ AbsArgs s (L.sP s₀) (L.dP s₀) (L.WW s₀) L.rate 0 (L.ml s₀))
    (.block (absArgs L.rate L.lenSrc)) := by
  obtain ⟨_, ht⟩ := hL.tAbs
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have a₀ := h.argEa (i := 0)
    have i₀ := h.argIn hp (i := 0) (by have := hL.one; omega)
    have v₀ := h.args 0 (by have := hL.one; omega)
    have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) hL.one
    have v₁ := h.args 1 hL.one
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    have e := ml_ofNat (L := L) (s₀ := s₀)
    apply WP.of_runBlock
    cases hm : L.mlen with
    | some k =>
      rw [hm] at e
      simp (config := {decide := true}) only [absArgs, Lay.lenSrc, hm, argOp, at_, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, a₀, i₀, v₀, ite_true, ite_false, Option.some.injEq, exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, rfl, rfl, by simp [e], by simp [h.esi]⟩⟩
    | none =>
      rw [hm] at e
      simp (config := {decide := true}) only [absArgs, Lay.lenSrc, hm, argOp, at_, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, a₀, i₀, v₀, a₁, i₁, v₁, ite_true, ite_false, Option.some.injEq,
        exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, rfl, rfl, by simp [e], by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.e1]


/-- `Ctx` after a call of a Keccak function that changes memory only within
parts of `scratch` and the stack below the frame. -/
theorem Ctx.call {s₀ s s' : State} (hL : L.Ok) (hp : Pre L s₀) (h : Ctx L s₀ s) (e₁ : s'.rd = s.rd)
    (e₂ : s'.wr = s.wr) (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region}
    (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, r ∈ [reg32 (L.sP s₀) 200, reg32 (L.sP s₀ + BitVec.ofNat 32 840) L.outlen,
      reg32 (L.WW s₀) 640, below (E1 s₀) 40]) : Ctx L s₀ s' := by
  have hs' := fun r hr => calls_sub hL hp r (hs r hr)
  refine ⟨h.toBase.call e₁ e₂ e₃ fr fun r hr => ?_, args_frame hp h.args fr fun r hr => ?_,
    by rw [e₃ .esi (by simp [calleeSaved]), h.esi]⟩
  · obtain ⟨r', h₁, h₂, -⟩ := hs' r hr; exact ⟨r', h₁, h₂⟩
  · obtain ⟨r', -, h₂, h₃⟩ := hs' r hr; exact h₃.symm.sub_right h₂

/-- `Ctx`, with the message absorbed. -/
structure A1 (L : Lay) (s₀ s : State) : Prop extends Ctx L s₀ s where
  st : Repr s.mem (L.sA s₀) L.rate (L.Msg s₀)

theorem absorb_call (hL : L.Ok) : Piece (Pre L) (PubP L)
    (fun s₀ s => Z L s₀ s ∧ AbsArgs s (L.sP s₀) (L.dP s₀) (L.WW s₀) L.rate 0 (L.ml s₀)) (A1 L)
    (callWith rs6 "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) := by
  refine absorb_piece' E1 L.sP L.dP L.WW L.rate L.ml hL.rate
    (fun s₀ hp => by have := hp.ml_lt; have := rate_lt hL.rate; omega) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.e1, hq.sP hL, hq.dP hL, by rw [Lay.WW, Lay.WW, hq.sP hL], hq.ml hL⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · have hk := hp.kbufs
    have hs := hp.s_fit
    refine ⟨h.esp, ha, hk, hp.d_fit, ?_, ?_, (hp.stk_d.sub_left hp.c_sub), ?_, hp.within_s0 h.wr (by omega),
      hp.within_s h.wr (by omega) (by omega)⟩
    · rw [Pre.reg_s0]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · rw [hp.reg_s (by omega)]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · refine ⟨L.dR s₀, ?_, 0, (BitVec.add_zero _).symm, by simp⟩
      rw [h.rd, h.wr, pushed_rd, hp.rd]; simp
  · refine ⟨h.toCtx.call hL hp e₁ e₂ e₃ fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
    · have := post [] (repr_nil h.st) (by simp)
      rwa [List.nil_append, h.msg hp] at this

/-! ## Padding -/

theorem padArgs_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (A1 L)
    (fun s₀ s => A1 L s₀ s ∧ PadArgs s (L.sP s₀) (L.WW s₀) L.rate (L.ml s₀) 0x1f)
    (.block (padArgs L.rate L.lenSrc)) := by
  obtain ⟨_, ht⟩ := hL.tPad
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) hL.one
    have v₁ := h.args 1 hL.one
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    have e := ml_ofNat (L := L) (s₀ := s₀)
    apply WP.of_runBlock
    cases hm : L.mlen with
    | some k =>
      rw [hm] at e
      simp (config := {decide := true}) only [padArgs, Lay.lenSrc, hm, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, ite_true, ite_false, Option.some.injEq, exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, by simp [e], rfl, by simp [h.esi]⟩⟩
    | none =>
      rw [hm] at e
      simp (config := {decide := true}) only [padArgs, Lay.lenSrc, hm, argOp, at_, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
        Option.map_some, Option.bind_some, a₁, i₁, v₁, ite_true, ite_false, Option.some.injEq,
        exists_eq_left']
      exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
        ⟨by simp [h.esi], rfl, by simp [e], rfl, by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.e1]

/-- `Ctx`, with the message absorbed and padded for SHAKE. -/
structure A2 (L : Lay) (s₀ s : State) : Prop extends Ctx L s₀ s where
  st : stateAt s.mem (L.sA s₀) = Proof.MlDsa.Sample.padded L.rate shakeSuffix (L.Msg s₀)

theorem pad_call (hL : L.Ok) : Piece (Pre L) (PubP L)
    (fun s₀ s => A1 L s₀ s ∧ PadArgs s (L.sP s₀) (L.WW s₀) L.rate (L.ml s₀) 0x1f) (A2 L)
    (callWith rs5 "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) := by
  refine pad_piece' E1 L.sP L.WW L.rate L.ml 0x1f hL.rate (fun s₀ hp => hp.ml_lt) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.e1, hq.sP hL, by rw [Lay.WW, Lay.WW, hq.sP hL], hq.ml hL⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · exact ⟨h.esp, ha, hp.kbufs, hp.within_s0 h.wr (by omega), hp.within_s h.wr (by omega) (by omega)⟩
  · refine ⟨h.toCtx.call hL hp e₁ e₂ e₃ fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h]
    · have := post (L.Msg s₀) h.st (by
        rw [bytesAt_length, Nat.mod_eq_of_lt hp.ml_lt])
      rwa [show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32] at this

/-! ## Squeezing -/

theorem sqArgs_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (A2 L)
    (fun s₀ s => A2 L s₀ s ∧
      AbsArgs s (L.sP s₀) (L.sP s₀ + BitVec.ofNat 32 840) (L.WW s₀) L.rate 0 L.outlen)
    (.block (sqzArgs L.rate L.outlen)) := by
  obtain ⟨_, ht⟩ := hL.tSqz
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht
  apply WP.of_runBlock
  simp (config := {decide := true}) only [sqzArgs, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.args, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, by simp [h.esi], rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the first `outlen` bytes of the XOF output of the message at
`scratch + 840`. -/
structure Out (L : Lay) (s₀ s : State) : Prop extends Ctx L s₀ s where
  out : ∀ p < L.outlen, s.mem (L.sA s₀ + BitVec.ofNat 64 (840 + p)) = (L.out s₀).getD p 0

theorem squeeze_call (hL : L.Ok) : Piece (Pre L) (PubP L)
    (fun s₀ s => A2 L s₀ s ∧
      AbsArgs s (L.sP s₀) (L.sP s₀ + BitVec.ofNat 32 840) (L.WW s₀) L.rate 0 L.outlen) (Out L)
    (callWith rs6 "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze) := by
  have ho := hL.out
  refine squeeze_piece E1 L.sP (fun s₀ => L.sP s₀ + BitVec.ofNat 32 840) L.WW L.rate 0 L.outlen hL.rate
    (by omega) (by omega) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.e1, hq.sP hL, by rw [hq.sP hL], by rw [Lay.WW, Lay.WW, hq.sP hL]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr r₁ _ => ?_)
  · have hs := hp.s_fit
    refine ⟨h.esp, ha, hp.kbufs, by rw [toNat_off (by omega)]; omega, ?_, ?_, ?_,
      hp.within_s0 h.wr (by omega), hp.within_s h.wr (by omega) (by omega),
      hp.within_s h.wr (by omega) (by omega)⟩
    · rw [hp.reg_s (by omega), Pre.reg_s0]
      exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [hp.reg_s (by omega), hp.reg_s (by omega)]
      exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [hp.reg_s (by omega)]
      exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · refine ⟨h.toCtx.call hL hp e₁ e₂ e₃ fr fun r hr => ?_, fun p hp' => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h]
    · rw [h.st, hp.off_eq (by omega)] at r₁
      have e := bytesAt_getD s'.mem (L.sA s₀ + BitVec.ofNat 64 840) (len := L.outlen) hp'
      rw [r₁, BitVec.add_assoc, ← BitVec.ofNat_add] at e
      exact e.symm

/-! ## The whole sponge -/

theorem sponge_piece (hL : L.Ok) : Piece (Pre L) (PubP L) (fun s₀ s => s = P0 s₀) (Out L)
    (sponge L.iS L.rate L.lenSrc L.outlen) :=
  Piece.seq (ld_piece hL) <| Piece.seq (zero_piece hL) <| Piece.seq (absArgs_piece hL) <|
    Piece.seq (absorb_call hL) <| Piece.seq (padArgs_piece hL) <| Piece.seq (pad_call hL) <|
    Piece.seq (sqArgs_piece hL) (squeeze_call hL)

end VG.Proof.MlDsa.X86.Sample
