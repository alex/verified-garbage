import VerifiedGarbage.Proof.MlDsa.Arm.Sign.BlockTr
import VerifiedGarbage.Proof.MlKem.Arm.Sample

/-!
# ML-DSA signing on ARMv7: SHAKE256 through the sponge functions

As on x86-64: zeroing the Keccak state at `scratch` (`kzero_ok`, from ML-KEM's
`zeroWords_ok`), and the calls of `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze` on it, with the working space at `scratch + 200`
(`kabs_ok`, `kpad_ok`, `ksqz_ok`, from ML-KEM's call lemmas of the sponge
functions in their frames, `Proof/MlKem/Arm/Keccak.lean`), and that two runs
in the same layout leak the same (`kabs_tr`, …).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (AbsorbArgs PadArgs SqueezeArgs absorb_ok pad_ok squeeze_ok absorb_ct pad_ct squeeze_ct
  regA below Kept)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-! ## Checks -/

/-- The Keccak state and the sponge functions' working space. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  inB wbs (sc 0) 200 && inB wbs (sc 200) 640 && inB bs (sc 0) 200 && inB bs (sc 200) 640 &&
    sepB bs (sc 0) 200 (sc 200) 640

/-- A piece of `len` bytes at `src` that `vg_keccak_absorb` reads. -/
def kabsChk (bs : List (Reg × Nat)) (src : Ptr) (len : Nat) : Bool :=
  inB bs src len && decide (src.1 ∈ bases) && decide (0 < len) && sepB bs src len (sc 0) 200 &&
    sepB bs src len (sc 200) 640

/-- The `len` bytes at `dst` that `vg_keccak_squeeze` writes. -/
def ksqzChk (bs wbs : List (Reg × Nat)) (dst : Ptr) (len : Nat) : Bool :=
  inB wbs dst len && inB bs dst len && decide (dst.1 ∈ bases) && decide (0 < len) && sepB bs (sc 0) 200 dst len &&
    sepB bs dst len (sc 200) 640

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem kChk_spec {bs wbs : List (Reg × Nat)} (h : kChk bs wbs = true) :
    inB wbs (sc 0) 200 = true ∧ inB wbs (sc 200) 640 = true ∧ inB bs (sc 0) 200 = true ∧
      inB bs (sc 200) 640 = true ∧ sepB bs (sc 0) 200 (sc 200) 640 = true := by
  simp only [kChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem kabsChk_spec {bs : List (Reg × Nat)} {src : Ptr} {len : Nat} (h : kabsChk bs src len = true) :
    inB bs src len = true ∧ src.1 ∈ bases ∧ 0 < len ∧ sepB bs src len (sc 0) 200 = true ∧
      sepB bs src len (sc 200) 640 = true := by
  simp only [kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ksqzChk_spec {bs wbs : List (Reg × Nat)} {dst : Ptr} {len : Nat} (h : ksqzChk bs wbs dst len = true) :
    inB wbs dst len = true ∧ inB bs dst len = true ∧ dst.1 ∈ bases ∧ 0 < len ∧
      sepB bs (sc 0) 200 dst len = true ∧ sepB bs dst len (sc 200) 640 = true := by
  simp only [ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rate_small {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 31 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- The 8 bytes of stack of a call of a sponge function, apart from the layout. -/
theorem k8 {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) {p : Ptr} {l : Nat}
    (h : inB (rbs ++ wbs) p l = true) (hsp : s1.sp = s.sp) : (below s1 8).Disjoint ⟨pa s p, l⟩ := by
  show (belowA s1.sp 8).Disjoint _
  rw [hsp]; exact (L.stkD h).sub_left (belowA_sub hD)

/-- What the sponge functions leave, as `PostB`. -/
theorem postB_kept {s s1 s' : State} (hD : 8 ≤ D) (k : Keep argRegs s s1) {rs : List Region} {W : List Region}
    (hk : Kept (rs ++ [below s1 8]) s1 s') (hW : ∀ r ∈ rs, r ∈ W) : PostB D s s' W ∧ CS s s' := by
  have hcs : CS s s' := fun r hr hl => (hk.cs r hr hl).trans (k.cs r hr hl)
  refine ⟨⟨hk.rd.trans k.rd, hk.wr.trans k.wr, fun r hr => hcs r (bases_cs r hr).1 (bases_cs r hr).2,
    hk.sp.trans k.sp, ?_⟩, hcs⟩
  rw [← k.mem]
  refine hk.frame.sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ (hW r hr), fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    show Region.Sub (belowA s1.sp 8) _
    rw [k.sp]; exact belowA_sub hD

/-! ## Zeroing the state -/

theorem kzero_ok {s : State} (L : Lay D rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true) :
    WP isa (.block kzero) s fun s' => PPostB D s s' [(sc 0, 200)] ∧ CS s s' ∧
      stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.zero := by
  obtain ⟨w0, _, i0, _, _⟩ := kChk_spec hk
  rw [kzero, VG.Impl.MlKem.Arm.zeroState, ← List.singleton_append, WP.block_append_iff]
  have hmov : WP isa (.block [.mov .r12 (.imm 0)]) s fun s₁ => s₁.gpr = (s.setReg .r12 0).gpr ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    run_block []
  refine WP.mono hmov fun s₁ ⟨g, m, rd, wr, sp⟩ => ?_
  have e7 : s₁.gpr .r7 = s.gpr .r7 := by rw [g]; simp [State.setReg]
  have ep : State.addr (s.gpr .r7) = pa s (sc 0) := by simp [pa]
  refine WP.mono (VG.Proof.MlKem.Arm.Sample.zeroWords_ok .r7 (s₁ := s₁) (by rw [g]; simp [State.setReg])
    (by rw [e7]; have := L.nwp i0; simpa using this) fun k hk => by
      rw [e7, wr, ep]
      exact inRegions_sub (L.iW w0) (by omega) (by decide))
    fun s₂ h₂ => ?_
  have hf := h₂.frame
  have hz := h₂.zero
  rw [e7, ep] at hf hz
  have hcs : CS s s₂ := fun r hr hl => by
    rw [h₂.gpr, g]
    simp [State.setReg, ne12_pres r hr hl]
  refine ⟨PostB.of_cs hcs (by rw [h₂.rd, rd]) (by rw [h₂.wr, wr]) (by rw [h₂.sp, sp]) (by rw [← m]; exact hf),
    hcs, VG.Proof.MlKem.Arm.Sample.stateAt_zero hz⟩

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .r7 = y.gpr .r7) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  block_tr (rs := [.r7]) (by decide) fun x y hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h x y hp

/-! ## Absorbing -/

theorem kabsOk {src : Ptr} {len rate pos : Nat} (b1 : src.1 ∈ bases) :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem kabsArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)] s s1)
    (k : Keep argRegs s s1) :
    AbsorbArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200)
      (s.gpr src.1 + BitVec.ofNat 32 src.2) rate pos len := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨is, _, l0, d0, d1⟩ := kabsChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  have hl : len < 2 ^ 32 := L.lenlt is
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have as : State.addr (s.gpr src.1 + BitVec.ofNat 32 src.2) = pa s src := L.pa32 is l0
  refine ⟨e1, e2, e3, e4, e5, e6, hrate, hpos, hl, by rw [k.sp]; have := L.sp; omega,
    L.fit (p := sc 0) i0 (by decide), L.fit is l0, L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [regA, a0, a1]; exact L.disj d01
  · simp only [regA, a0, as]; exact L.disj d0
  · simp only [regA, a1, as]; exact L.disj d1
  · simp only [regA, a0]; exact k8 L hD i0 k.sp
  · simp only [regA, a1]; exact k8 L hD i1 k.sp
  · simp only [regA, as]; exact k8 L hD is k.sp
  · simp only [regA, a0, a1]; rw [k.wr]; exact Covers.cons (L.cW w0) (L.cW w1)
  · simp only [regA, as]; rw [k.rd, k.wr]; exact L.cR is

theorem kabs_ok {s : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    WP isa (kabs src len rate pos) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧ CS s s' ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        Repr s'.mem (pa s (sc 0)) rate (msg ++ bytesAt s.mem (pa s src) len) := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  obtain ⟨is, b1, l0, _, _⟩ := kabsChk_spec hc
  refine WP.seq (WP.mono (setArgs_ok _ (kabsOk b1) s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have as : State.addr (s.gpr src.1 + BitVec.ofNat 32 src.2) = pa s src := L.pa32 is l0
  refine absorb_ok (kabsArgs L hD hk hc hrate hpos hA k) fun s' hkept hR _ => ?_
  simp only [regA, a0, a1] at hkept
  obtain ⟨hP, hcs⟩ := postB_kept (W := [toR s (sc 0, 200), toR s (sc 200, 640)]) hD k
    (rs := [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, fun msg hmsg hpos' => ?_⟩
  rw [k.mem, a0, as] at hR
  exact hR msg hmsg hpos'

theorem kabs_tr (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {src : Ptr} {len rate pos : Nat}
    (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    RelCT isa (LRel D rbs wbs) (kabs src len rate pos) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := kChk_spec hk
  obtain ⟨is, b1, _, _, _⟩ := kabsChk_spec hc
  refine RelCT.seq (setArgs_rel (kabsOk b1)) (absorb_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, _, kabsArgs R.lx hD hk hc hrate hpos hAx kx, ?_⟩
  rw [R.eq i0, R.eq is]
  exact kabsArgs R.ly hD hk hc hrate hpos hAy ky

/-! ## Padding -/

theorem kpadOk {rate pos suffix : Nat} :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok]

/-- The moves of `pad`'s arguments. -/
theorem kpadMoves_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) :
    WP isa (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr] as)) s fun s1 =>
      (∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip as, s1.gpr da.1 = da.2.val s) ∧ Keep argRegs s s1 :=
  WP.mono (setArgsTo_ok _ as (by decide) (by decide) ha s) fun _ ⟨h, k⟩ => ⟨h, k.mono (by decide)⟩

theorem kpadArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate)
    (hA : ∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
      s1.gpr da.1 = da.2.val s)
    (k : Keep argRegs s s1) :
    PadArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200) rate pos (BitVec.ofNat 32 suffix) := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := kChk_spec hk
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  refine ⟨hA (.r0, .ptr (sc 0)) (by simp), hA (.r1, .imm rate) (by simp), hA (.r2, .imm pos) (by simp),
    hA (.r3, .imm suffix) (by simp), hA (.lr, .ptr (sc 200)) (by simp), hrate, hpos, by rw [k.sp]; have := L.sp; omega,
    L.fit (p := sc 0) i0 (by decide), L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_⟩
  · simp only [regA, a0, a1]; exact L.disj d01
  · simp only [regA, a0]; exact k8 L hD i0 k.sp
  · simp only [regA, a1]; exact k8 L hD i1 k.sp
  · simp only [regA, a0, a1]; rw [k.wr]; exact Covers.cons (L.cW w0) (L.cW w1)

theorem b8_ofNat32 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 32 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem kpad_ok {s : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    WP isa (kpad rate pos suffix) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧ CS s s' ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (pa s (sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  refine WP.seq (WP.mono (kpadMoves_ok _ kpadOk s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  refine pad_ok (kpadArgs L hD hk hrate hpos hA k) fun s' hkept hR => ?_
  simp only [regA, a0, a1] at hkept
  obtain ⟨hP, hcs⟩ := postB_kept (W := [toR s (sc 0, 200), toR s (sc 200, 640)]) hD k
    (rs := [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, fun msg hmsg hpos' => ?_⟩
  rw [k.mem, a0] at hR
  rw [hR msg hmsg hpos', b8_ofNat32 hs]

theorem kpad_tr (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {rate pos suffix : Nat} (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    RelCT isa (LRel D rbs wbs) (kpad rate pos suffix) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := kChk_spec hk
  have hm : RelCT isa (LRel D rbs wbs) (.block (setArgsTo [.r0, .r1, .r2, .r3, .lr]
      [.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)])) fun x1 y1 => ∃ x y, LRel D rbs wbs x y ∧
      ((∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
        x1.gpr da.1 = da.2.val x) ∧ Keep argRegs x x1) ∧
      ((∀ da ∈ [Reg.r0, .r1, .r2, .r3, .lr].zip [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)],
        y1.gpr da.1 = da.2.val y) ∧ Keep argRegs y y1) :=
    RelCT.mono (RelCT.wpDep (block_nomem_tr (setArgsTo_nomem _ _))
      (fun x y _ => ⟨kpadMoves_ok _ kpadOk x, kpadMoves_ok _ kpadOk y⟩)) (fun _ _ h => h)
      fun _ _ ⟨_, x, y, hp, h1, h2⟩ => ⟨x, y, hp, h1, h2⟩
  refine RelCT.seq hm (pad_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, kpadArgs R.lx hD hk hrate hpos hAx kx, ?_⟩
  rw [R.eq i0]
  exact kpadArgs R.ly hD hk hrate hpos hAy ky

/-! ## Squeezing -/

theorem ksqzOk {dst : Ptr} {len rate : Nat} (b1 : dst.1 ∈ bases) :
    [Arg.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem ksqzArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates)
    (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)] s s1)
    (k : Keep argRegs s s1) :
    SqueezeArgs s1 (s.gpr .r7 + BitVec.ofNat 32 0) (s.gpr .r7 + BitVec.ofNat 32 200)
      (s.gpr dst.1 + BitVec.ofNat 32 dst.2) rate 0 len := by
  obtain ⟨w0, w1, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨wd, id, _, l0, d0, d1⟩ := ksqzChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  have hl : len < 2 ^ 32 := L.lenlt id
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have ad : State.addr (s.gpr dst.1 + BitVec.ofNat 32 dst.2) = pa s dst := L.pa32 id l0
  refine ⟨e1, e2, e3, e4, e5, e6, hrate, Nat.zero_le _, hl, by rw [k.sp]; have := L.sp; omega,
    L.fit (p := sc 0) i0 (by decide), L.fit id l0, L.fit (p := sc 200) i1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [regA, a0, ad]; exact L.disj d0
  · simp only [regA, a0, a1]; exact L.disj d01
  · simp only [regA, a1, ad]; exact L.disj d1
  · simp only [regA, a0]; exact k8 L hD i0 k.sp
  · simp only [regA, ad]; exact k8 L hD id k.sp
  · simp only [regA, a1]; exact k8 L hD i1 k.sp
  · simp only [regA, a0, a1, ad]; rw [k.wr]; exact Covers.cons (L.cW w0) (Covers.cons (L.cW wd) (L.cW w1))

theorem ksqz_ok {s : State} (L : Lay D rbs wbs s) (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    WP isa (ksqz rate dst len) s fun s' => PPostB D s s' [(sc 0, 200), (dst, len), (sc 200, 640)] ∧ CS s s' ∧
      bytesAt s'.mem (pa s dst) len = squeezeFrom rate (stateAt s.mem (pa s (sc 0))) 0 len := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  obtain ⟨wd, id, b1, l0, _, _⟩ := ksqzChk_spec hc
  refine WP.seq (WP.mono (setArgs_ok _ (ksqzOk b1) s) fun s1 ⟨hA, k⟩ => ?_)
  have a0 : State.addr (s.gpr .r7 + BitVec.ofNat 32 0) = pa s (sc 0) := L.pa32 (p := sc 0) i0 (by decide)
  have a1 : State.addr (s.gpr .r7 + BitVec.ofNat 32 200) = pa s (sc 200) := L.pa32 (p := sc 200) i1 (by decide)
  have ad : State.addr (s.gpr dst.1 + BitVec.ofNat 32 dst.2) = pa s dst := L.pa32 id l0
  refine squeeze_ok (ksqzArgs L hD hk hc hrate hA k) fun s' hkept ho _ _ => ?_
  simp only [regA, a0, a1, ad] at hkept
  obtain ⟨hP, hcs⟩ := postB_kept (W := [toR s (sc 0, 200), toR s (dst, len), toR s (sc 200, 640)]) hD k
    (rs := [⟨pa s (sc 0), 200⟩, ⟨pa s dst, len⟩, ⟨pa s (sc 200), 640⟩]) hkept (fun r hr => hr)
  refine ⟨hP, hcs, ?_⟩
  rw [ad, a0, k.mem] at ho
  exact ho

theorem ksqz_tr (hD : 8 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {dst : Ptr} {len rate : Nat}
    (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    RelCT isa (LRel D rbs wbs) (ksqz rate dst len) fun _ _ => True := by
  obtain ⟨_, _, i0, _, _⟩ := kChk_spec hk
  obtain ⟨_, id, b1, _, _, _⟩ := ksqzChk_spec hc
  refine RelCT.seq (setArgs_rel (ksqzOk b1)) (squeeze_ct fun x1 y1 ⟨x, y, R, ⟨hAx, kx⟩, ⟨hAy, ky⟩⟩ => ?_)
  refine ⟨by rw [kx.sp, ky.sp, R.sp], _, _, _, _, _, _, ksqzArgs R.lx hD hk hc hrate hAx kx, ?_⟩
  rw [R.eq i0, R.eq id]
  exact ksqzArgs R.ly hD hk hc hrate hAy ky

end

end VG.Proof.MlDsa.Arm.Sign
