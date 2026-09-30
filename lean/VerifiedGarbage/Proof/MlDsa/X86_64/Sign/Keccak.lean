import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Glue
import VerifiedGarbage.Proof.MlKem.X86_64.KCall

/-!
# ML-DSA signing on x86-64: SHAKE256 through the sponge functions

Untrusted: everything here is checked by Lean. Zeroing the Keccak state at
`scratch` (`kzero_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` on it, with the working space at
`scratch + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`, from the sponge
functions' own call lemmas, `Proof/MlKem/X86_64/KCall.lean`); then
`shakeAt ps out len`, which zeroes the state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: the output of the sponge from the padded
state of their concatenation (`shake_ok`), leaking only the addresses
(`shake_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep WP.keep AbsorbArgs PadArgs SqueezeArgs absorb_pre pad_pre squeeze_pre absorb_call
  pad_call squeeze_call)
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
  inB bs src len && decide (src.1 ∈ bases) && decide (src.2 < 2 ^ 31) && decide (len < 2 ^ 31) &&
    sepB bs src len (sc 0) 200 && sepB bs src len (sc 200) 640

/-- The `len` bytes at `dst` that `vg_keccak_squeeze` writes. -/
def ksqzChk (bs wbs : List (Reg × Nat)) (dst : Ptr) (len : Nat) : Bool :=
  inB wbs dst len && inB bs dst len && decide (dst.1 ∈ bases) && decide (dst.2 < 2 ^ 31) && decide (len < 2 ^ 31) &&
    sepB bs (sc 0) 200 dst len && sepB bs dst len (sc 200) 640

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem kChk_spec {bs wbs : List (Reg × Nat)} (h : kChk bs wbs = true) :
    inB wbs (sc 0) 200 = true ∧ inB wbs (sc 200) 640 = true ∧ inB bs (sc 0) 200 = true ∧
      inB bs (sc 200) 640 = true ∧ sepB bs (sc 0) 200 (sc 200) 640 = true := by
  simp only [kChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem kabsChk_spec {bs : List (Reg × Nat)} {src : Ptr} {len : Nat} (h : kabsChk bs src len = true) :
    inB bs src len = true ∧ src.1 ∈ bases ∧ src.2 < 2 ^ 31 ∧ len < 2 ^ 31 ∧ sepB bs src len (sc 0) 200 = true ∧
      sepB bs src len (sc 200) 640 = true := by
  simp only [kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem ksqzChk_spec {bs wbs : List (Reg × Nat)} {dst : Ptr} {len : Nat} (h : ksqzChk bs wbs dst len = true) :
    inB wbs dst len = true ∧ inB bs dst len = true ∧ dst.1 ∈ bases ∧ dst.2 < 2 ^ 31 ∧ len < 2 ^ 31 ∧
      sepB bs (sc 0) 200 dst len = true ∧ sepB bs dst len (sc 200) 640 = true := by
  simp only [ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The 16 bytes of stack of a call of a sponge function, from the layout. -/
theorem k16 {s : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) {p : Ptr} {l : Nat} (h : inB (rbs ++ wbs) p l = true)
    {s1 : State} (hsp : s1.gpr .rsp = s.gpr .rsp) : (below (s1.gpr .rsp) 16).Disjoint ⟨pa s p, l⟩ := by
  rw [hsp]; exact (L.stkD h).sub_left (below_sub (by omega) (by have := L.dsm; omega))

theorem rate_small {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 31 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-! ## Zeroing the state -/

theorem zeroStep_ok (b : Reg) (d : Nat) (s : State) (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (VG.Impl.MlKem.X86_64.at_ b d) .rax]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr .rax)) ∧ Keep [] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hw]

theorem lane_sep (p : Addr) {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * i)) (64 / 8) (p + BitVec.ofNat 64 (8 * j)) (64 / 8) := by
  intro x hx hy
  simp only [Nat.reduceDiv] at hx hy
  bv_omega

/-- The lanes at `b + off`, zeroed. -/
theorem zeroSt_ok (b : Reg) (off : Nat) (s : State) (h0 : s.gpr .rax = 0)
    (hw : ∀ i < 25, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (zeroSt b off)) s fun s' =>
      stateAt s'.mem (s.gpr b + BitVec.ofNat 64 off) = Spec.Sha3.zero ∧
        Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧ Keep [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 64 = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, hz⟩ => ⟨?_, hf, hk⟩
  · have hb : s'.gpr b = s.gpr b := hk'.gpr (by simp)
    have ha : s'.gpr .rax = 0 := by rw [hk'.gpr (by simp), h0]
    have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    refine WP.mono (zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
      fun s'' ⟨hm, hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
    · rw [hm, hb, e]
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · rw [hm, hb, e, ha]
      by_cases hjk : j = k
      · subst hjk; rw [Mem.readW_writeW_self64]
      · rw [Mem.readW_writeW_sep (lane_sep _ (by omega) hk hjk) (by decide), hz j (by omega)]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact hz i hi

theorem kzero_ok {s : State} (L : Lay D rbs wbs s) (hk : kChk (rbs ++ wbs) wbs = true) :
    WP isa (.block kzero) s fun s' => PPostB D s s' [(sc 0, 200)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.zero := by
  obtain ⟨w0, _, _, _, _⟩ := kChk_spec hk
  rw [kzero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = s.mem ∧ s1.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm, hax⟩, k1⟩ => ?_
  have hbx : s1.gpr .rbx = s.gpr .rbx := k1.gpr (by decide)
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => ?_) fun s2 ⟨hz, hf, k2⟩ => ?_
  · rw [k1.2.2, hbx]
    have h0 := L.iW w0
    exact inRegions_sub (off := 8 * i) (l := 8) h0 (by omega) (by decide)
  · have k : Keep [.rax] s s2 := (k1.trans k2).mono fun r hr => by simpa using hr
    rw [hbx] at hz hf
    have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s.gpr r := fun r hr => k.gpr fun h => by
      simp only [List.mem_singleton] at h; subst h; exact absurd hr (by decide)
    refine ⟨⟨k.2.1, k.2.2, fun r hr => hcs r (bases_cs r hr), hcs .rsp (by decide), ?_⟩, hcs, hz⟩
    rw [hm] at hf
    exact hf.mono fun r hr => List.mem_append_left _ hr

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h x y hp) (by taint_decide)

/-! ## Absorbing -/

theorem kabsArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)] s s1)
    (hsp : s1.gpr .rsp = s.gpr .rsp) :
    AbsorbArgs s1 (pa s (sc 0)) (pa s src) (pa s (sc 200)) rate pos len := by
  obtain ⟨_, _, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨is, _, _, hl, d0, d1⟩ := kabsChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  exact ⟨e1, e2, e3, e4, e5, e6, hrate, hpos,
    by omega, L.disj d01, L.disj d0, L.disj d1, k16 L hD i0 hsp, k16 L hD is hsp, k16 L hD i1 hsp⟩

theorem kabsOk {bs : List (Reg × Nat)} {src : Ptr} {len rate pos : Nat} (hc : kabsChk bs src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) : [Arg.ptr (sc 0), .imm rate, .imm pos, .ptr src, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  obtain ⟨_, b1, o1, hl, _, _⟩ := kabsChk_spec hc
  have := rate_small hrate
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true,
    decide_eq_true (show rate < 2 ^ 32 by omega), decide_eq_true (show pos < 2 ^ 32 by omega),
    decide_eq_true (show len < 2 ^ 32 by omega)]
  decide

theorem kabs_ok {s : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {src : Ptr} {len rate pos : Nat} (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates)
    (hpos : pos < rate) :
    WP isa (kabs src len rate pos) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        Repr s'.mem (pa s (sc 0)) rate (msg ++ bytesAt s.mem (pa s src) len) := by
  obtain ⟨w0, w1, _, _, _⟩ := kChk_spec hk
  obtain ⟨is, _, _, _, _, _⟩ := kabsChk_spec hc
  refine WP.seq (WP.mono (setArgs_ok _ (kabsOk hc hrate hpos) s) fun s1 ⟨⟨hA, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have cW : Covers [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] s1.wr := by
    rw [k.2.2]; exact covers_cons (L.cW w0) (L.cW w1)
  refine absorb_call (kabsArgs L hD hk hc hrate hpos hA hsp)
    (covers_append (by rw [k.2.1, k.2.2]; exact L.cR is) (covers_wr cW)) cW
    fun s' hrd hwr hcs hf hR _ => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r (bases_cs r hr), k.gpr (argRegs_cs r (bases_cs r hr))],
      by rw [hcs .rsp (by decide), hsp], ?_⟩, fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩
  · rw [← hm, ← hsp]
    have := Frame.below_mono (wr := [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) (by simpa using hf)
      (show 16 ≤ D by omega) (by have := L.dsm; omega)
    exact this
  · intro msg hmsg hpos'
    rw [← hm] at hmsg ⊢
    exact hR msg hmsg hpos'

theorem kabs_tr (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {src : Ptr} {len rate pos : Nat}
    (hc : kabsChk (rbs ++ wbs) src len = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    RelCT isa (LRel D rbs wbs) (kabs src len rate pos) fun _ _ => True := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  obtain ⟨is, _, _, _, _, _⟩ := kabsChk_spec hc
  refine callP_tr Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
    (kabsOk hc hrate hpos) fun x y x1 y1 R ⟨⟨hAx, _⟩, kx⟩ ⟨⟨hAy, _⟩, ky⟩ => ?_
  have hsx : x1.gpr .rsp = x.gpr .rsp := kx.gpr (by decide)
  have hsy : y1.gpr .rsp = y.gpr .rsp := ky.gpr (by decide)
  have ax := kabsArgs R.lx hD hk hc hrate hpos hAx hsx
  have ay := kabsArgs R.ly hD hk hc hrate hpos hAy hsy
  refine ⟨_, _, _, _, absorb_pre ax, absorb_pre ay, ?_,
    covers_append (by rw [kx.2.1, kx.2.2]; exact R.lx.cR is) (covers_wr (by rw [kx.2.2]; exact covers_cons (R.lx.cW w0) (R.lx.cW w1))),
    by rw [kx.2.2]; exact covers_cons (R.lx.cW w0) (R.lx.cW w1),
    covers_append (by rw [ky.2.1, ky.2.2]; exact R.ly.cR is) (covers_wr (by rw [ky.2.2]; exact covers_cons (R.ly.cW w0) (R.ly.cW w1))),
    by rw [ky.2.2]; exact covers_cons (R.ly.cW w0) (R.ly.cW w1), by rw [hsx, hsy, R.rsp]⟩
  simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    ax.rdi, ax.rsi, ax.rdx, ax.rcx, ax.r8, ax.r9, ay.rdi, ay.rsi, ay.rdx, ay.rcx, ay.r8, ay.r9, R.pa i0, R.pa i1,
    R.pa is, hsx, hsy, R.rsp, and_self]

/-! ## Padding -/

theorem kpadArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate)
    (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)] s s1)
    (hsp : s1.gpr .rsp = s.gpr .rsp) :
    PadArgs s1 (pa s (sc 0)) (pa s (sc 200)) rate pos := by
  obtain ⟨_, _, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨e1, e2, e3, _, e5⟩ := argsIn5 hA
  exact ⟨e1, e2, e3, e5, hrate, hpos, L.disj d01, k16 L hD i0 hsp, k16 L hD i1 hsp⟩

theorem kpadOk {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    [Arg.ptr (sc 0), .imm rate, .imm pos, .imm suffix, .ptr (sc 200)].all Arg.ok = true := by
  have := rate_small hrate
  simp only [List.all_cons, List.all_nil, Arg.ok, Bool.and_true,
    decide_eq_true (show rate < 2 ^ 32 by omega), decide_eq_true (show pos < 2 ^ 32 by omega),
    decide_eq_true (show suffix < 2 ^ 32 by omega)]
  decide

theorem b8_ofNat64 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 64 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem kpad_ok {s : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate pos suffix : Nat} (hrate : rate ∈ rates) (hpos : pos < rate) (hs : suffix < 256) :
    WP isa (kpad rate pos suffix) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      ∀ msg, Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (pa s (sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  obtain ⟨w0, w1, _, _, _⟩ := kChk_spec hk
  refine WP.seq (WP.mono (setArgs_ok _ (kpadOk hrate hpos hs) s) fun s1 ⟨⟨hA, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have cW : Covers [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] s1.wr := by
    rw [k.2.2]; exact covers_cons (L.cW w0) (L.cW w1)
  have hcx : s1.gpr .rcx = BitVec.ofNat 64 suffix := (argsIn5 hA).2.2.2.1
  refine pad_call (kpadArgs L hD hk hrate hpos hA hsp) (covers_append covers_nil (covers_wr cW)) cW
    fun s' hrd hwr hcs hf hR => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r (bases_cs r hr), k.gpr (argRegs_cs r (bases_cs r hr))],
      by rw [hcs .rsp (by decide), hsp], ?_⟩, fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩
  · rw [← hm, ← hsp]
    exact Frame.below_mono (wr := [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) (by simpa using hf)
      (show 16 ≤ D by omega) (by have := L.dsm; omega)
  · intro msg hmsg hpos'
    rw [← hm] at hmsg
    rw [hR msg hmsg hpos', hcx, b8_ofNat64 hs]

theorem kpad_tr (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {rate pos suffix : Nat} (hrate : rate ∈ rates)
    (hpos : pos < rate) (hs : suffix < 256) :
    RelCT isa (LRel D rbs wbs) (kpad rate pos suffix) fun _ _ => True := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  refine callP_tr Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
    (kpadOk hrate hpos hs) fun x y x1 y1 R ⟨⟨hAx, _⟩, kx⟩ ⟨⟨hAy, _⟩, ky⟩ => ?_
  have hsx : x1.gpr .rsp = x.gpr .rsp := kx.gpr (by decide)
  have hsy : y1.gpr .rsp = y.gpr .rsp := ky.gpr (by decide)
  have ax := kpadArgs R.lx hD hk hrate hpos hAx hsx
  have ay := kpadArgs R.ly hD hk hrate hpos hAy hsy
  refine ⟨_, _, _, _, pad_pre ax, pad_pre ay, ?_,
    covers_append covers_nil (covers_wr (by rw [kx.2.2]; exact covers_cons (R.lx.cW w0) (R.lx.cW w1))),
    by rw [kx.2.2]; exact covers_cons (R.lx.cW w0) (R.lx.cW w1),
    covers_append covers_nil (covers_wr (by rw [ky.2.2]; exact covers_cons (R.ly.cW w0) (R.ly.cW w1))),
    by rw [ky.2.2]; exact covers_cons (R.ly.cW w0) (R.ly.cW w1), by rw [hsx, hsy, R.rsp]⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
    ax.rdi, ax.rsi, ax.rdx, ax.r8, ay.rdi, ay.rsi, ay.rdx, ay.r8, R.pa i0, R.pa i1, hsx, hsy, R.rsp, and_self]

/-! ## Squeezing -/

theorem ksqzArgs {s s1 : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates)
    (hA : ArgsIn [.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)] s s1)
    (hsp : s1.gpr .rsp = s.gpr .rsp) :
    SqueezeArgs s1 (pa s (sc 0)) (pa s dst) (pa s (sc 200)) rate 0 len := by
  obtain ⟨_, _, i0, i1, d01⟩ := kChk_spec hk
  obtain ⟨_, id, _, _, hl, d0, d1⟩ := ksqzChk_spec hc
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := argsIn6 hA
  exact ⟨e1, e2, e3, e4, e5, e6, hrate, Nat.zero_le _,
    by omega, L.disj d0, L.disj d01, L.disj d1, k16 L hD i0 hsp, k16 L hD id hsp, k16 L hD i1 hsp⟩

theorem ksqzOk {bs wbs : List (Reg × Nat)} {dst : Ptr} {len rate : Nat} (hc : ksqzChk bs wbs dst len = true) (hrate : rate ∈ rates) :
    [Arg.ptr (sc 0), .imm rate, .imm 0, .ptr dst, .imm len, .ptr (sc 200)].all Arg.ok = true := by
  obtain ⟨_, _, b1, o1, hl, _, _⟩ := ksqzChk_spec hc
  have := rate_small hrate
  simp only [List.all_cons, List.all_nil, Arg.ok, b1, o1, decide_true, Bool.and_true,
    decide_eq_true (show rate < 2 ^ 32 by omega), decide_eq_true (show len < 2 ^ 32 by omega)]
  decide

theorem ksqz_ok {s : State} (L : Lay D rbs wbs s) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {dst : Ptr} {len rate : Nat} (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    WP isa (ksqz rate dst len) s fun s' => PPostB D s s' [(sc 0, 200), (dst, len), (sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s dst) len = squeezeFrom rate (stateAt s.mem (pa s (sc 0))) 0 len := by
  obtain ⟨w0, w1, _, _, _⟩ := kChk_spec hk
  obtain ⟨wd, _, _, _, _, _, _⟩ := ksqzChk_spec hc
  refine WP.seq (WP.mono (setArgs_ok _ (ksqzOk hc hrate) s) fun s1 ⟨⟨hA, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have cW : Covers [⟨pa s (sc 0), 200⟩, ⟨pa s dst, len⟩, ⟨pa s (sc 200), 640⟩] s1.wr := by
    rw [k.2.2]; exact covers_cons (L.cW w0) (covers_cons (L.cW wd) (L.cW w1))
  refine squeeze_call (ksqzArgs L hD hk hc hrate hA hsp) (covers_append covers_nil (covers_wr cW)) cW
    fun s' hrd hwr hcs hf ho => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r (bases_cs r hr), k.gpr (argRegs_cs r (bases_cs r hr))],
      by rw [hcs .rsp (by decide), hsp], ?_⟩, fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩
  · rw [← hm, ← hsp]
    exact Frame.below_mono (wr := [⟨pa s (sc 0), 200⟩, ⟨pa s dst, len⟩, ⟨pa s (sc 200), 640⟩]) (by simpa using hf)
      (show 16 ≤ D by omega) (by have := L.dsm; omega)
  · rw [ho, hm]

theorem ksqz_tr (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true) {dst : Ptr} {len rate : Nat}
    (hc : ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    RelCT isa (LRel D rbs wbs) (ksqz rate dst len) fun _ _ => True := by
  obtain ⟨w0, w1, i0, i1, _⟩ := kChk_spec hk
  obtain ⟨wd, id, _, _, _, _, _⟩ := ksqzChk_spec hc
  refine callP_tr Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
    (ksqzOk hc hrate) fun x y x1 y1 R ⟨⟨hAx, _⟩, kx⟩ ⟨⟨hAy, _⟩, ky⟩ => ?_
  have hsx : x1.gpr .rsp = x.gpr .rsp := kx.gpr (by decide)
  have hsy : y1.gpr .rsp = y.gpr .rsp := ky.gpr (by decide)
  have ax := ksqzArgs R.lx hD hk hc hrate hAx hsx
  have ay := ksqzArgs R.ly hD hk hc hrate hAy hsy
  refine ⟨_, _, _, _, squeeze_pre ax, squeeze_pre ay, ?_,
    covers_append covers_nil (covers_wr (by rw [kx.2.2]; exact covers_cons (R.lx.cW w0) (covers_cons (R.lx.cW wd) (R.lx.cW w1)))),
    by rw [kx.2.2]; exact covers_cons (R.lx.cW w0) (covers_cons (R.lx.cW wd) (R.lx.cW w1)),
    covers_append covers_nil (covers_wr (by rw [ky.2.2]; exact covers_cons (R.ly.cW w0) (covers_cons (R.ly.cW wd) (R.ly.cW w1)))),
    by rw [ky.2.2]; exact covers_cons (R.ly.cW w0) (covers_cons (R.ly.cW wd) (R.ly.cW w1)), by rw [hsx, hsy, R.rsp]⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
    ax.rdi, ax.rsi, ax.rdx, ax.rcx, ax.r8, ax.r9, ay.rdi, ay.rsi, ay.rdx, ay.rcx, ay.r8, ay.r9, R.pa i0, R.pa i1,
    R.pa id, hsx, hsy, R.rsp, and_self]

end

end VG.Proof.MlDsa.X86_64.Sign
