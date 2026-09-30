import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.MlKem.X86_64.KCall
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt`, correctness

Untrusted: everything here is checked by Lean. The function runs in
pieces, each from a state satisfying an invariant (`I1` … `I6`, relative
to the entry state `σ`) to the next. `snSample n` runs the three calls of
the sponge, whose output is `XOF(B, 3 n)` (`xof_eq`), and the loop, which
then samples `sampleAfter [] (xofByte B) n` (`sample_ok`). After 168
iterations these are `sampleAfter [] (xofByte B) 280` if there are 256 of
them (`sampleAfter_full`), and otherwise the function runs the 280
iterations (`more_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- `vg_mlkem_sample_ntt(seed = rdi, a = rsi, scratch = rdx) -> eax`, with
16 bytes of stack below `rsp`. -/
def sampleK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 34⟩] ∧ s.wr = [pR (s.gpr .rsi), ⟨s.gpr .rdx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 34⟩ (pR (s.gpr .rsi)) ∧ Region.Disjoint ⟨s.gpr .rdi, 34⟩ ⟨s.gpr .rdx, 2048⟩ ∧
    (pR (s.gpr .rsi)).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rsi)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧ (s.gpr .rdx).toNat + 2048 ≤ 2 ^ 64
  post s s' :=
    (s'.gpr .rax).setWidth 32 = (if (sampleNTT minIterations (bytesAt s.mem (s.gpr .rdi) 34)).isSome then 1 else 0) ∧
      ∀ f, sampleNTT minIterations (bytesAt s.mem (s.gpr .rdi) 34) = some f → PolyIs s'.mem (s.gpr .rsi) f
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdi) 34 = bytesAt s₂.mem (s₂.gpr .rdi) 34

namespace SampleNtt

theorem sx200 : BitVec.signExtend 64 (200 : BitVec 32) = BitVec.ofNat 64 200 := by decide
theorem sx840 : BitVec.signExtend 64 (840 : BitVec 32) = BitVec.ofNat 64 840 := by decide

theorem r12_not {r : Reg} (hr : r ∈ [Reg.r12, .r13, .r14, .r15]) :
    r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rsi
abbrev scr : Addr := σ.gpr .rdx
/-- The seed. -/
abbrev B : List Byte := bytesAt σ.mem (sd σ) 34
abbrev scrR : Region := ⟨scr σ, 2048⟩
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := scr σ + BitVec.ofNat 64 off
end

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = scr σ
  rbp : s.gpr .rbp = aP σ
  rsp : s.gpr .rsp = σ.gpr .rsp
  cs : ∀ r ∈ [Reg.r12, .r13, .r14, .r15], s.gpr r = σ.gpr r
  saved : s.mem.readW (at' σ 1680) 64 = σ.gpr .rbx ∧ s.mem.readW (at' σ 1688) 64 = σ.gpr .rbp ∧
    s.mem.readW (at' σ 1696) 64 = sd σ
  frame : Frame [pR (aP σ), scrR σ, below (σ.gpr .rsp) 16] σ.mem s.mem

section
variable {σ : State} (hp : sampleK.pre σ)
include hp

theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨at' σ a, n⟩ (scrR σ) :=
  sub_offset' h (by have := hp.2.2.2.2.2.2.2.2.2.2.2; omega)

omit hp in
theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨scr σ, n⟩ (scrR σ) := Region.sub_prefix h

omit hp in
theorem disj_scr {a n b m : Nat} (h : a + n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨at' σ a, n⟩ ⟨at' σ b, m⟩ := off_disj h (by omega)

omit hp in
theorem disj_scr0 {n b m : Nat} (h : n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨scr σ, n⟩ ⟨at' σ b, m⟩ := by
  have := disj_scr (σ := σ) (a := 0) (n := n) (by omega) hb
  simpa [at', add_ofNat_zero] using this

/-- A sub-region of the scratch space is apart from the seed. -/
theorem seed_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Disjoint ⟨sd σ, 34⟩ ⟨at' σ a, n⟩ :=
  hp.2.2.2.1.sub_right (sub_scr hp h)

theorem stk_scr {a n : Nat} (h : a + n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨at' σ a, n⟩ :=
  hp.2.2.2.2.2.2.2.2.2.2.1.sub_right (sub_scr hp h)

theorem seed_scr0 {n : Nat} (h : n ≤ 2048) : Region.Disjoint ⟨sd σ, 34⟩ ⟨scr σ, n⟩ :=
  hp.2.2.2.1.sub_right (sub_scr0 h)

theorem stk_scr0 {n : Nat} (h : n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨scr σ, n⟩ :=
  hp.2.2.2.2.2.2.2.2.2.2.1.sub_right (sub_scr0 h)

/-- The seed is not written. -/
theorem seed_frame {s : State} (he : Env σ s) : bytesAt s.mem (sd σ) 34 = B σ :=
  bytesAt_frame he.frame (by simpa using ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.2.2.2.2.1.symm⟩) (by decide)

theorem low_sub {a n : Nat} (h : a + n ≤ 1680) : Region.Sub ⟨at' σ a, n⟩ ⟨scr σ, 1680⟩ :=
  sub_offset' h (by have := hp.2.2.2.2.2.2.2.2.2.2.2; omega)

omit hp in
/-- The values saved in `scratch[1680..1704)` are kept by writes apart from them. -/
theorem Env.saved_frame {s s' : State} (he : Env σ s) {rs : List Region}
    (hd : ∀ k, 1680 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ rs, (⟨at' σ k, 8⟩ : Region).Disjoint r)
    (hf : Frame rs s.mem s'.mem) :
    s'.mem.readW (at' σ 1680) 64 = σ.gpr .rbx ∧ s'.mem.readW (at' σ 1688) 64 = σ.gpr .rbp ∧
      s'.mem.readW (at' σ 1696) 64 = sd σ := by
  rw [hf.readW (Region.contains_self _ _) (hd 1680 (by omega) (by omega)) (by decide),
    hf.readW (Region.contains_self _ _) (hd 1688 (by omega) (by omega)) (by decide),
    hf.readW (Region.contains_self _ _) (hd 1696 (by omega) (by omega)) (by decide)]
  exact he.saved

/-- A call that writes within the first 1680 bytes of the scratch space and
the stack keeps `Env`. -/
theorem Env.call {s s' : State} (he : Env σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨scr σ, 1680⟩)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (rs ++ [below (s.gpr .rsp) 16]) s.mem s'.mem) : Env σ s' := by
  have hsp : s'.gpr .rsp = s.gpr .rsp := hcs .rsp (by simp [calleeSaved])
  have hd : ∀ k, 1680 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ rs ++ [below (s.gpr .rsp) 16],
      (⟨at' σ k, 8⟩ : Region).Disjoint r := by
    intro k hk hk' r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ((disj_scr0 (σ := σ) (n := 1680) (b := k) (m := 8) hk hk').symm).sub_right (hrs r hr)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [he.rsp]; exact (stk_scr hp hk').symm
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hcs .rbx (by simp [calleeSaved]), he.rbx],
    by rw [hcs .rbp (by simp [calleeSaved]), he.rbp], by rw [hsp, he.rsp], fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr', he.cs r hr]
  · exact he.saved_frame hd hf
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scrR σ, by simp, fun x h => sub_scr0 (σ := σ) (n := 1680) (by omega) x (hrs r hr x h)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (σ.gpr .rsp) 16, by simp, by rw [he.rsp]; exact fun _ h => h⟩

/-! ## The prologue -/

/-- The arguments of `absorb`, after zeroing the state. -/
structure I1 (σ s : State) : Prop where
  env : Env σ s
  zero : stateAt s.mem (scr σ) = Spec.Sha3.zero
  args : AbsorbArgs s (scr σ) (sd σ) (at' σ 200) 168 0 34

theorem inScr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions s.wr (scr σ + BitVec.ofNat 64 a) n := by
  rw [hw, hp.2.1]
  exact ⟨scrR σ, by simp, contains_offset' h (by omega)⟩

omit hp in
/-- `Env` after a block that writes only caller-saved registers and no memory. -/
theorem Env.keep {s s' : State} (he : Env σ s) (hm : s'.mem = s.mem)
    (hk : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s') : Env σ s' :=
  ⟨hk.2.1.trans he.rd, hk.2.2.trans he.wr, by rw [hk.gpr (by decide), he.rbx], by rw [hk.gpr (by decide), he.rbp],
    by rw [hk.gpr (by decide), he.rsp], fun r hr => by rw [hk.gpr (r12_not hr), he.cs r hr],
    by rw [hm]; exact he.saved, by rw [hm]; exact he.frame⟩

/-- The seed and the scratch space in the regions. -/
theorem regions {s : State} (he : Env σ s) : s.rd ++ s.wr = [⟨sd σ, 34⟩, pR (aP σ), scrR σ] := by
  rw [he.rd, he.wr, hp.1, hp.2.1]; rfl

theorem cov_scr {s : State} (he : Env σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = scr σ + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨scrR σ, by rw [he.wr, hp.2.1]; simp, off, hb, hl⟩

theorem cov_all {s : State} (he : Env σ s) {rs : List Region}
    (h : ∀ r ∈ rs, r = ⟨sd σ, 34⟩ ∨ ∃ off, r.base = scr σ + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers rs (s.rd ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [regions hp he]
    rcases h r hr with rfl | ⟨off, hb, hl⟩
    · exact ⟨⟨sd σ, 34⟩, by simp, 0, (add_ofNat_zero _).symm, by simp⟩
    · exact ⟨scrR σ, by simp, off, hb, hl⟩


/-- Zeroing the state, and the arguments of `absorb`, from `rcx` = `seed`. -/
theorem abs_ok {s : State} (he : Env σ s) (hcx : s.gpr .rcx = sd σ) : WP isa (.block snAbs) s (I1 σ) := by
  unfold snAbs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm1, hax⟩, k1⟩ => ?_
  have he1 := he.keep hm1 (k1.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => by
      rw [he1.rbx, add_ofNat_zero]; exact inScr hp he1.wr (by omega)) fun s2 ⟨hz, hf2, k2⟩ => ?_
  rw [he1.rbx, add_ofNat_zero] at hz hf2
  have he2 : Env σ s2 := Env.call hp he1 (rs := [⟨scr σ, 200⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega))
    k2.2.1 k2.2.2 (fun r _ => k2.gpr (by simp)) (hf2.mono (by simp))
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r8, .r9] (Q := fun s => s.mem = s2.mem ∧
      s.gpr .rdi = scr σ ∧ s.gpr .rsi = BitVec.ofNat 64 168 ∧ s.gpr .rdx = BitVec.ofNat 64 0 ∧
      s.gpr .r8 = BitVec.ofNat 64 34 ∧ s.gpr .r9 = at' σ 200)
    (by xrun [he2.rbx, sx200]) (by decide)) fun s3 ⟨⟨hm3, hdi, hsi, hdx, h8, h9⟩, k3⟩ => ?_
  have he3 := he2.keep hm3 (k3.mono (by decide))
  refine ⟨he3, by rw [hm3]; exact hz,
    ⟨hdi, hsi, hdx, by rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hcx], h8, h9, by decide,
      by decide, by decide, disj_scr0 (by omega) (by omega), seed_scr0 hp (by omega), seed_scr hp (by omega),
      by rw [he3.rsp]; exact stk_scr0 hp (by omega), by rw [he3.rsp]; exact hp.2.2.2.2.2.2.2.2.1,
      by rw [he3.rsp]; exact stk_scr hp (by omega)⟩⟩

theorem proA_ok : WP isa (.block snPro) σ (I1 σ) := by
  unfold snPro
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx, .rbp, .rcx] (Q := fun s =>
      s.mem = ((σ.mem.writeW (at' σ 1680) (σ.gpr .rbx)).writeW (at' σ 1688) (σ.gpr .rbp)).writeW (at' σ 1696)
          (σ.gpr .rdi) ∧
        s.gpr .rbx = scr σ ∧ s.gpr .rbp = aP σ ∧ s.gpr .rcx = sd σ)
    (by xrun [inScr hp rfl (a := 1680) (n := 8) (by omega), inScr hp rfl (a := 1688) (n := 8) (by omega),
      inScr hp rfl (a := 1696) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, hbp, hcx⟩, k1⟩ => abs_ok hp ?_ hcx
  have sep : ∀ a b, a + 8 ≤ b → b + 8 ≤ 2048 →
      Mem.Sep (at' σ a) (64 / 8) (at' σ b) (64 / 8) ∧ Mem.Sep (at' σ b) (64 / 8) (at' σ a) (64 / 8) :=
    fun a b h hb => ⟨(disj_scr (σ := σ) (n := 8) (m := 8) h hb).sep (Region.contains_self _ _)
      (Region.contains_self _ _), (disj_scr (σ := σ) (n := 8) (m := 8) h hb).symm.sep (Region.contains_self _ _)
      (Region.contains_self _ _)⟩
  have hin : ∀ a, a + 8 ≤ 2048 → (scrR σ).Contains (at' σ a) (64 / 8) := fun a ha =>
    contains_offset' (by omega) (by omega)
  refine ⟨k1.2.1, k1.2.2, hbx, hbp, k1.gpr (by decide), fun r hr => k1.gpr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide), ?_, ?_⟩
  · rw [hm1, Mem.readW_writeW_sep (sep 1680 1696 (by omega) (by omega)).1 (by decide),
      Mem.readW_writeW_sep (sep 1680 1688 (by omega) (by omega)).1 (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 1688 1696 (by omega) (by omega)).1 (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_self64]
    exact ⟨rfl, rfl, rfl⟩
  · rw [hm1]
    exact (((Frame.refl _ _).writeW (by simp) _ (hin 1680 (by omega))).writeW (by simp) _
      (hin 1688 (by omega))).writeW (by simp) _ (hin 1696 (by omega))

/-! ## The sponge -/

/-- After absorbing the seed. -/
structure I2 (σ s : State) : Prop where
  env : Env σ s
  repr : Spec.Sha3.Repr s.mem (scr σ) 168 (B σ)

theorem covA {s : State} (he : Env σ s) :
    Covers ([⟨sd σ, 34⟩] ++ [⟨scr σ, 200⟩, ⟨at' σ 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨scr σ, 200⟩, ⟨at' σ 200, 640⟩] s.wr := by
  refine ⟨cov_all hp he ?_, cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inl rfl, .inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]

theorem subA : ∀ r ∈ [(⟨scr σ, 200⟩ : Region), ⟨at' σ 200, 640⟩], Region.Sub r ⟨scr σ, 1680⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [Region.sub_prefix (by omega), low_sub hp (by omega)]

theorem callB_ok {s : State} (h : I1 σ s) : WP isa (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb) s (I2 σ) := by
  refine absorb_call h.args (covA hp h.env).1 (covA hp h.env).2 fun s' hrd hwr hcs hf hr _ =>
    ⟨Env.call hp h.env (subA hp) hrd hwr hcs hf, ?_⟩
  have := hr [] (Proof.MlKem.repr_nil h.zero) rfl
  rwa [List.nil_append, seed_frame hp h.env] at this

/-- The arguments of `pad`. -/
structure I3 (σ s : State) : Prop where
  env : Env σ s
  repr : Spec.Sha3.Repr s.mem (scr σ) 168 (B σ)
  args : PadArgs s (scr σ) (at' σ 200) 168 34
  rcx : (s.gpr .rcx).setWidth 8 = Spec.Sha3.shakeSuffix

theorem blkC_ok {s : State} (h : I2 σ s) : WP isa (.block snPadArgs) s (I3 σ) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = scr σ ∧ s'.gpr .rsi = BitVec.ofNat 64 168 ∧ s'.gpr .rdx = BitVec.ofNat 64 34 ∧
      s'.gpr .rcx = BitVec.setWidth 64 (0x1f : BitVec 32) ∧ s'.gpr .r8 = at' σ 200)
    (by unfold snPadArgs; xrun [h.env.rbx, sx200]) (by decide)) fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  refine ⟨he, by rw [hm]; exact h.repr, ⟨hdi, hsi, hdx, h8, by decide, by decide, disj_scr0 (by omega) (by omega),
    by rw [he.rsp]; exact stk_scr0 hp (by omega), by rw [he.rsp]; exact stk_scr hp (by omega)⟩, by rw [hcx]; decide⟩

/-- After padding. -/
structure I4 (σ s : State) : Prop where
  env : Env σ s
  st : stateAt s.mem (scr σ) = Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B σ)

theorem covP {s : State} (he : Env σ s) :
    Covers ([] ++ [⟨scr σ, 200⟩, ⟨at' σ 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨scr σ, 200⟩, ⟨at' σ 200, 640⟩] s.wr :=
  ⟨fun a n h => (covA hp he).1 a n (by simp only [List.nil_append] at h; exact
    ⟨_, List.mem_append_right _ h.choose_spec.1, h.choose_spec.2⟩), (covA hp he).2⟩

theorem callD_ok {s : State} (h : I3 σ s) : WP isa (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad) s (I4 σ) := by
  refine pad_call h.args (covP hp h.env).1 (covP hp h.env).2 fun s' hrd hwr hcs hf hst =>
    ⟨Env.call hp h.env (subA hp) hrd hwr hcs hf, ?_⟩
  rw [hst (B σ) h.repr (by rw [bytesAt_length]), h.rcx]

/-- The arguments of `squeeze`, for `len` bytes. -/
structure I5 (σ : State) (len : Nat) (s : State) : Prop where
  env : Env σ s
  st : stateAt s.mem (scr σ) = Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B σ)
  args : SqueezeArgs s (scr σ) (at' σ 840) (at' σ 200) 168 0 len

theorem blkE_ok {n : BitVec 32} {len : Nat} (hn : (3 * n).toNat = len) (hl : len ≤ 840) {s : State} (h : I4 σ s) :
    WP isa (.block (snSqzArgs (3 * n))) s (I5 σ len) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = scr σ ∧ s'.gpr .rsi = BitVec.ofNat 64 168 ∧ s'.gpr .rdx = BitVec.ofNat 64 0 ∧
      s'.gpr .rcx = at' σ 840 ∧ s'.gpr .r8 = BitVec.setWidth 64 (3 * n) ∧ s'.gpr .r9 = at' σ 200)
    (by unfold snSqzArgs; xrun [h.env.rbx, sx200, sx840]) rfl)
    fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  rw [← BitVec.ofNat_toNat, hn] at h8
  refine ⟨he, by rw [hm]; exact h.st, ⟨hdi, hsi, hdx, hcx, h8, h9, by decide, by decide, by omega,
    disj_scr0 (by omega) (by omega), disj_scr0 (by omega) (by omega),
    (disj_scr (σ := σ) (a := 200) (n := 640) (b := 840) (m := len) (by omega) (by omega)).symm,
    by rw [he.rsp]; exact stk_scr0 hp (by omega), by rw [he.rsp]; exact stk_scr hp (by omega),
    by rw [he.rsp]; exact stk_scr hp (by omega)⟩⟩

/-- After squeezing `len` bytes: the XOF output. -/
structure I6 (σ : State) (len : Nat) (s : State) : Prop where
  env : Env σ s
  out : bytesAt s.mem (at' σ 840) len = xof (B σ) len

theorem covS {s : State} (he : Env σ s) {len : Nat} (hl : len ≤ 840) :
    Covers ([] ++ [⟨scr σ, 200⟩, ⟨at' σ 840, len⟩, ⟨at' σ 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨scr σ, 200⟩, ⟨at' σ 840, len⟩, ⟨at' σ 200, 640⟩] s.wr := by
  refine ⟨cov_all hp he ?_, cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨840, rfl, by simp; omega⟩, .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩]

theorem subS {len : Nat} (hl : len ≤ 840) : ∀ r ∈ [(⟨scr σ, 200⟩ : Region), ⟨at' σ 840, len⟩, ⟨at' σ 200, 640⟩],
    Region.Sub r ⟨scr σ, 1680⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [Region.sub_prefix (by omega), low_sub hp (by omega), low_sub hp (by omega)]

theorem callF_ok {len : Nat} (hl : len ≤ 840) {s : State} (h : I5 σ len s) :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze) s (I6 σ len) := by
  refine squeeze_call h.args (covS hp h.env hl).1 (covS hp h.env hl).2 fun s' hrd hwr hcs hf ho =>
    ⟨Env.call hp h.env (subS hp hl) hrd hwr hcs hf, ?_⟩
  rw [ho, h.st, xof_eq]

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := sampleAfter [] (xofByte (B σ)) t

/-- At the start of iteration `t` of `N`. -/
structure LAt (σ : State) (N t : Nat) (s : State) : Prop where
  env : Env σ s
  out : bytesAt s.mem (at' σ 840) (3 * N) = xof (B σ) (3 * N)
  rsi : s.gpr .rsi = at' σ 840 + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (N - t)
  stored : Stored s.mem (aP σ) (Lt σ t)

omit hp in
theorem out_byte {N t : Nat} {s : State} (h : LAt σ N t s) {k : Nat} (hk : 3 * t + k < 3 * N) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 k) = xofByte (B σ) (3 * t + k) := by
  have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [bytesAt_getD _ _ hk, xof_getD _ hk] at this
  rw [h.rsi, off_add]; exact this

theorem lat_regions {N t : Nat} (hN : N ≤ 280) {s : State} (h : LAt σ N t s) {k : Nat} (hk : 3 * t + k < 3 * N) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 k) 1 := by
  rw [regions hp h.env, h.rsi, off_add, off_add]
  exact ⟨scrR σ, by simp, contains_offset' (by omega) (by omega)⟩

/-- An iteration, from `LAt`. -/
theorem lat_step {N t : Nat} (hN : N ≤ 280) (ht : t < N) {s : State} (h : LAt σ N t s) :
    WP isa snBody s fun s' => LAt σ N (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (N - t) - 1 == 0) := by
  have hL : (Lt σ t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  have hw : pR (aP σ) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  refine WP.mono (snBody_ok s (aP := aP σ) h.env.rbp h.rdi hL (WrA.of_mem hw) h.stored
    (by simpa using lat_regions hp hN h (k := 0) (by omega)) (lat_regions hp hN h (by omega))
    (lat_regions hp hN h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := out_byte h (k := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  rw [e0, out_byte h (k := 1) (by omega), out_byte h (k := 2) (by omega), ← sampleAfter_succ] at hdi hst
  have hd : ∀ r ∈ [pR (aP σ)], (⟨at' σ 840, 3 * N⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.2.2.2.2.1.symm.sub_left (sub_scr hp (by omega))
  have dA : ∀ k, 1680 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ [pR (aP σ)], (⟨at' σ k, 8⟩ : Region).Disjoint r :=
    fun k _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.2.2.2.2.1.symm.sub_left (sub_scr hp hk)
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (r12_not hr), h.env.cs r hr], h.env.saved_frame dA hf,
    h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [bytesAt_frame hf hd (by omega)]; exact h.out, by rw [hsi, h.rsi,
      show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, off_add, Nat.mul_succ], hdi,
    by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩

omit hp in
/-- After the first block of the loop's setup. -/
structure IA (σ : State) (N : Nat) (s : State) : Prop where
  env : Env σ s
  out : bytesAt s.mem (at' σ 840) (3 * N) = xof (B σ) (3 * N)
  rsi : s.gpr .rsi = at' σ 840
  rdi : s.gpr .rdi = 0

omit hp in
theorem latA {N : Nat} {s : State} (h : I6 σ (3 * N) s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s (IA σ N) := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = at' σ 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ?_
  exact ⟨h.env.keep hm1 (k1.mono (by decide)), by rw [hm1]; exact h.out, hsi1, hdi1⟩

omit hp in
theorem latB {n : BitVec 32} {N : Nat} (hn : n.toNat = N) {s : State} (h : IA σ N s) :
    WP isa (.block [.mov32 .rcx (.imm n)]) s (LAt σ N 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.setWidth 64 n)
    (by xrun) rfl) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.env.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.out, by rw [k2.gpr (by decide), h.rsi]; simp,
    by rw [k2.gpr (by decide), h.rdi]; rfl, by rw [hcx, ← BitVec.ofNat_toNat, hn]; rfl,
    fun k hk => absurd hk (by simp [sampleAfter_zero])⟩

omit hp in
theorem zf_last {N t : Nat} (hN : N ≤ 280) (ht : t < N) :
    (BitVec.ofNat 64 (N - t) - 1 == 0) = decide (t + 1 = N) := by
  rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

/-- `N` iterations of the loop. -/
theorem loop_ok {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (hN0 : 0 < N) (hN : N ≤ 280) {s : State}
    (h : I6 σ (3 * N) s) : WP isa (snLoop n) s (LAt σ N N) := by
  unfold snLoop
  refine WP.seq (WP.mono (latA h) fun s1 h1 => WP.seq (WP.mono (latB hn h1) fun s2 h2 => ?_))
  refine WP.loop (M := isa) (fun m s => ∃ t, m = N - t ∧ t < N ∧ LAt σ N t s) ?_ N s2 ⟨0, by omega, hN0, h2⟩
  rintro m s ⟨t, rfl, ht, hI⟩
  refine WP.mono (lat_step hp hN ht hI) fun s' ⟨hI', hz'⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (t + 1 = N)) := by
    show s'.zf.map (!·) = _
    rw [hz', zf_last hN ht]; rfl
  by_cases hl : t + 1 = N
  · exact .inl ⟨by rw [he, decide_eq_true hl]; rfl, by subst hl; exact hI'⟩
  · exact .inr ⟨by rw [he, decide_eq_false hl]; rfl, _, by omega, t + 1, rfl, by omega, hI'⟩

/-- `snSample n`: the sponge, and `N` iterations of the loop. -/
theorem sample_ok {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (h3 : (3 * n).toNat = 3 * N) (hN0 : 0 < N)
    (hN : N ≤ 280) {s : State} (h : I1 σ s) : WP isa (snSample n) s (LAt σ N N) := by
  unfold snSample
  exact WP.seq (WP.mono (callB_ok hp h) fun s2 h2 => WP.seq (WP.mono (blkC_ok hp h2) fun s3 h3' =>
    WP.seq (WP.mono (callD_ok hp h3') fun s4 h4 => WP.seq (WP.mono (blkE_ok hp h3 (by omega) h4) fun s5 h5 =>
      WP.seq (WP.mono (callF_ok hp (by omega) h5) fun s6 h6 => loop_ok hp hn hN0 hN h6)))))

/-! ## The second run and the end -/

/-- The coefficients sampled. -/
abbrev Ls (σ : State) : List Zq := Lt σ 280

/-- The end: the postcondition and the calling convention. -/
def Fin (σ s : State) : Prop := sampleK.post σ s ∧ gprPreserved σ s

/-- After the loops. -/
structure IEnd (σ s : State) : Prop where
  env : Env σ s
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Ls σ).length
  stored : Stored s.mem (aP σ) (Ls σ)

omit hp in
/-- 168 iterations that sampled 256 coefficients sampled all of them. -/
theorem ls_full (hf : (Lt σ 168).length = 256) : Ls σ = Lt σ 168 :=
  sampleAfter_full (by rw [n_eq]; exact hf) 280 (by omega)

/-- `seed` in `rcx`, and `snAbs`. -/
theorem redo_ok {s : State} (he : Env σ s) :
    WP isa (.block (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs)) s (I1 σ) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 1696) 8 := by
    rw [regions hp he, he.rbx]; exact ⟨scrR σ, by simp, contains_offset' (by omega) (by omega)⟩
  rw [show (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs : List Instr) = [.mov .rcx (.mem (at_ .rbx 1696))] ++ snAbs
    from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rcx = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 1696) 64) (by xrun [hin]) (by decide))
    fun s1 ⟨⟨hm, hcx⟩, k⟩ => abs_ok hp (he.keep hm (k.mono (by decide))) ?_
  rw [hcx, he.rbx]; exact he.saved.2.2

/-- After the check of `j`. -/
structure IM (σ s : State) : Prop where
  env : Env σ s
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ 168).length
  stored : Stored s.mem (aP σ) (Lt σ 168)
  cf : s.cf = some (decide ((Lt σ 168).length < 256))

omit hp in
theorem cmp_ok {s : State} (h : LAt σ 168 168 s) : WP isa (.block [.alu .cmp .rdi (.imm 256)]) s (IM σ) := by
  refine WP.mono (cmpRdi_ok s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_
  have hL : (Lt σ 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  have hk : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  rw [h.rdi, ofNat64_toNat (by omega)] at hc
  exact ⟨h.env.keep hm (hk.mono (by simp)), by rw [hk.gpr (by simp), h.rdi], by rw [hm]; exact h.stored, hc⟩

/-- The 280 iterations, from the start. -/
theorem redo_all_ok {s : State} (he : Env σ s) :
    WP isa (.seq (.block (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs)) (snSample 280)) s (IEnd σ) :=
  WP.seq (WP.mono (redo_ok hp he) fun _ h2 =>
    WP.mono (sample_ok hp (n := 280) (N := 280) (by decide) (by decide) (by omega) (by omega) h2) fun _ h3 =>
      ⟨h3.env, h3.rdi, h3.stored⟩)

omit hp in
/-- Without them, if `j = 256`. -/
theorem skip_ok {s : State} (h : IM σ s) (hb : s.cf = some false) : IEnd σ s := by
  have hL : (Lt σ 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  have hf : (Lt σ 168).length = 256 := by
    rw [h.cf, Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  exact ⟨h.env, by rw [h.rdi, ls_full hf], by rw [ls_full hf]; exact h.stored⟩

/-- The check of `j`, and the 280 iterations if it is less than 256. -/
theorem more_ok {s : State} (h : LAt σ 168 168 s) : WP isa snMore s (IEnd σ) := by
  unfold snMore
  refine WP.seq (WP.mono (cmp_ok h) fun s1 h1 => ?_)
  exact WP.ite _ h1.cf (fun _ => redo_all_ok hp h1.env) fun hb => WP.block_nil (skip_ok h1 (by rw [h1.cf, hb]))

omit hp in
theorem ret_below (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 16) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

omit hp in
theorem epi_ok (s : State) (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 1688) 8)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 1680) 8) :
    WP isa (.block snEpi) s fun s' =>
      (s'.gpr .rax = s.gpr .rdi >>> 8 ∧ s'.gpr .rbp = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 1688) 64 ∧
        s'.gpr .rbx = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 1680) 64 ∧ s'.mem = s.mem) ∧
      Keep [.rax, .rbp, .rbx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold snEpi
  xrun [h8, h0]

omit hp in
theorem stored_polyAt {m : Mem} {aP : Addr} {L : List Zq} (h : Stored m aP L) (hL : L.length = 256) :
    Reduced m aP ∧ polyAt m aP = toPoly L := by
  have hv : ∀ i < 256, (coeffAt m aP i).toNat = (L.getD i 0).val := fun i hi => by
    rw [h i (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt (L.getD i 0); omega)]
  refine ⟨fun i hi => by rw [hv i hi]; exact val_lt _, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [polyAt, toPoly, Vector.getElem_ofFn, hv i hi, ofNat_val]

theorem end_ok {s : State} (h : IEnd σ s) : WP isa (.block snEpi) s (Fin σ) := by
  have hbx2 : s.gpr .rbx = scr σ := h.env.rbx
  have hrr2 := regions hp h.env
  have hsv := h.env.saved
  refine WP.mono (epi_ok s (by rw [hrr2, hbx2]; exact ⟨scrR σ, by simp, contains_offset' (by omega) (by omega)⟩)
    (by rw [hrr2, hbx2]; exact ⟨scrR σ, by simp, contains_offset' (by omega) (by omega)⟩))
    fun s3 ⟨⟨hax, hbp, hbx, hm3⟩, k3⟩ => ?_
  rw [hbx2] at hbp hbx
  have hL : (Ls σ).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 280
  have hr : (s3.gpr .rax).setWidth 32 = BitVec.ofNat 32 ((Ls σ).length / 256) := by
    apply BitVec.eq_of_toNat_eq
    rw [hax, h.rdi, BitVec.toNat_setWidth, shr_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (Ls σ).length) (by omega)]
  have hfr : Frame [pR (aP σ), scrR σ, below (σ.gpr .rsp) 16] σ.mem s3.mem := by
    rw [hm3]; exact h.env.frame
  refine ⟨?_, fun r hr' => ?_, ?_⟩
  · by_cases hfull : (Ls σ).length = 256
    · have e1 : (s3.gpr .rax).setWidth 32 = 1 := by rw [hr, hfull]; rfl
      obtain ⟨hred, hpoly⟩ := stored_polyAt (m := s3.mem) (aP := aP σ) (by rw [hm3]; exact h.stored) hfull
      have hs : sampleNTT minIterations (B σ) = some (toPoly (Ls σ)) :=
        sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact hfull)
      refine ⟨by rw [e1, hs]; rfl, fun f hf => ?_⟩
      rw [hs] at hf
      rw [← Option.some.inj hf]
      exact ⟨hred, hpoly⟩
    · have e0 : (s3.gpr .rax).setWidth 32 = 0 := by rw [hr, Nat.div_eq_of_lt (by omega)]; rfl
      have hs : sampleNTT minIterations (B σ) = none := sampleNTT_none (by rw [n_eq]; exact hfull)
      refine ⟨by rw [e0, hs]; rfl, fun f hf => ?_⟩
      rw [hs] at hf
      exact absurd hf (Option.some_ne_none f).symm
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbx.trans hsv.1
    · exact hbp.trans hsv.2.1
    all_goals rw [k3.gpr (by decide)]
    · exact h.env.rsp
    all_goals exact h.env.cs _ (by decide)
  · exact hfr.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, ret_below _⟩) (by decide)

end

end SampleNtt

theorem sample_correct (σ : State) (hp : sampleK.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.sampleNTT σ t s' ∧ abiPreserved σ s' ∧ sampleK.post σ s' := by
  open SampleNtt in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (proA_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (sample_ok hp (n := 168) (N := 168) (by decide) (by decide) (by omega) (by omega) h1) fun s2 h2 =>
      WP.seq (WP.mono (more_ok hp h2) fun s3 h3 => end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlKem.X86_64
