import VerifiedGarbage.Proof.Hmac.PPC64LE.Common
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.PPC64LE.Contract

/-!
# HMAC-SHA-256 on PPC64LE: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Hmac.Common.Finalize`). The two SHA-256
finalizations are calls of `vg_sha256_finalize`, used as a black box through
its proof (`WP.callF`), inside the frame saving the link register
(`WP.frameReg`): the first into `scratch[176..208)`, the second into `out`.
-/

namespace VG.Proof.Hmac.PPC64LE.Finalize

open VG VG.PPC64LE VG.Impl.Hmac.PPC64LE
open VG.Impl.Sha256.PPC64LE.Stream (mov)
open VG.Proof.Hmac.PPC64LE
open VG.Proof.Hmac.Common (writeBytes_at writeBytes_other bytesAt_getD' bytesAt_length
  bytesAt_writeBytes_self bytesAt_writeBytes_sep stateAt_eq_of_bytes)
open VG.Proof.Hmac.Common (xorPad_length repr_outer)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.PPC64LE (contains_offset sub_offset toNat_ofNat_lt)
open VG.Proof.Sha256.PPC64LE.Stream (Upd Mupd wp_mov wp_li wp_addi wp_std wp_ld frame_bytes
  write_frame_bytes readW_writeW_save frame_sub)
open VG.Proof.Sha256.PPC64LE.Stream.WP (cons)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .r3
/-- The outer state. -/
abbrev out : Addr := s₀.gpr .r4
/-- Where the MAC goes (`out` in the Rust signature). -/
abbrev mac : Addr := s₀.gpr .r6
abbrev scr : Addr := s₀.gpr .r7
abbrev inR : Region := ⟨inn s₀, 96⟩
abbrev outR : Region := ⟨out s₀, 96⟩
abbrev macR : Region := ⟨mac s₀, 32⟩
abbrev scR : Region := ⟨scr s₀, 248⟩
/-- Where a finalization into `o` may write (besides its frame). -/
abbrev finW (o : Addr) : List Region := [inR s₀, ⟨o, 32⟩, ⟨scr s₀, 160⟩]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outR s₀]
  wr : s₀.wr = [inR s₀, macR s₀, scR s₀]
  i_o : (inR s₀).Disjoint (outR s₀)
  i_m : (inR s₀).Disjoint (macR s₀)
  i_s : (inR s₀).Disjoint (scR s₀)
  o_m : (outR s₀).Disjoint (macR s₀)
  o_s : (outR s₀).Disjoint (scR s₀)
  m_s : (macR s₀).Disjoint (scR s₀)

/-- The frame a call of `vg_sha256_finalize` pushes, below the stack pointer
`s` has, is disjoint from the buffers. -/
structure Stack (s : State) : Prop where
  sp48 : 48 ≤ s.sp.toNat
  i : (below s.sp 48).Disjoint (inR s)
  o : (below s.sp 48).Disjoint (outR s)
  m : (below s.sp 48).Disjoint (macR s)
  s : (below s.sp 48).Disjoint (scR s)

/-- On entry: our frame and the callee's are in the 96 bytes below the stack
pointer, disjoint from the buffers. -/
structure Stack₀ (s₀ : State) : Prop where
  sp96 : 96 ≤ s₀.sp.toNat
  i : (below s₀.sp 96).Disjoint (inR s₀)
  o : (below s₀.sp 96).Disjoint (outR s₀)
  m : (below s₀.sp 96).Disjoint (macR s₀)
  s : (below s₀.sp 96).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Hmac.finalizeSha256PPC64LE.pre s₀) : Pre s₀ ∧ Stack₀ s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13⟩⟩

/-! ## The calls of `vg_sha256_finalize` -/

theorem fin_exec : ∀ s, Proof.Sha256.finalizePPC64LE.pre s → ∃ t s',
    Exec isa Impl.Sha256.PPC64LE.Stream.finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Sha256.finalizePPC64LE.post s s' := by
  intro s hs
  have h := Proof.Sha256.PPC64LE.Stream.Finalize.pre_of hs
  obtain ⟨t, s', he, h₁, h₂⟩ := Proof.Sha256.PPC64LE.Stream.Finalize.correct h.1 h.2
  exact ⟨t, s', he, h₁, h₂⟩

theorem fin_fdepth : Impl.Sha256.PPC64LE.Stream.finalize.fdepth = 1 := by decide +kernel

theorem sub176 (s₀ : State) : Region.Sub ⟨scr s₀ + 176, 32⟩ (scR s₀) :=
  sub_offset (off := 176) (by omega) (by omega)

theorem sub160 (s₀ : State) : Region.Sub ⟨scr s₀, 160⟩ (scR s₀) := Region.sub_prefix (by omega)

/-- A call of `vg_sha256_finalize` on the inner state, with its digest at `o`
(`scratch[176..208)` or `out`) and `scratch[0..160)` as its scratch space. -/
theorem fin_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {o : Addr}
    (hio : (inR s₀).Disjoint ⟨o, 32⟩) (hos : Region.Disjoint ⟨o, 32⟩ ⟨scr s₀, 160⟩)
    (hso : (below s₀.sp 48).Disjoint ⟨o, 32⟩)
    (hcov : ∃ r' ∈ [inR s₀, macR s₀, scR s₀], ∃ off, o = r'.base + BitVec.ofNat 64 off ∧ off + 32 ≤ r'.len)
    {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h0 : s.gpr .r3 = inn s₀) (h3 : s.gpr .r6 = scr s₀) (h2 : s.gpr .r5 = o)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (finW s₀ o ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, Repr s.mem (inn s₀) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem o 32 = Spec.Sha256.hash m) → Q s') :
    WP isa sha256Finalize s Q := by
  have c0 : s.callEntry.gpr .r3 = inn s₀ := (State.callEntry_gpr _ (by decide)).trans h0
  have c2 : s.callEntry.gpr .r5 = o := (State.callEntry_gpr _ (by decide)).trans h2
  have c3 : s.callEntry.gpr .r6 = scr s₀ := (State.callEntry_gpr _ (by decide)).trans h3
  refine WP.callF (k := Proof.Sha256.finalizePPC64LE) fin_exec (rd := []) (wr := finW s₀ o) ?_ ?_ ?_ ?_
    (by rw [fin_fdepth]; decide)
  · simp only [Proof.Sha256.finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c2, c3, hsp]
    exact ⟨trivial, trivial, hio, hp.i_s.sub_right (sub160 s₀), hos, hs.sp48, hs.i, hso,
      hs.s.sub_right (sub160 s₀)⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · obtain ⟨r', hr', off, h₁, h₂⟩ := hcov
      exact ⟨r', List.mem_append_right _ hr', off, h₁, h₂⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
    · exact hcov
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' h₁ h₂ h₃ h₄ hcs hpost
    simp only [Proof.Sha256.finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c2] at hpost
    rw [fin_fdepth, hsp] at h₄
    exact hQ s' h₁ h₂ h₃ h₄ hcs fun m hr hc => hpost Spec.Sha256.H0 m hr hc

/-- The first call: the digest into `scratch[176..208)`. -/
theorem fin1_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h0 : s.gpr .r3 = inn s₀) (h3 : s.gpr .r6 = scr s₀) (h2 : s.gpr .r5 = scr s₀ + 176)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (finW s₀ (scr s₀ + 176) ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, Repr s.mem (inn s₀) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (scr s₀ + 176) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa sha256Finalize s Q :=
  fin_ok hp hs (hp.i_s.sub_right (sub176 s₀))
    (by intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega)
    (hs.s.sub_right (sub176 s₀)) ⟨scR s₀, by simp, 176, rfl, by simp⟩ hrd hwr hsp h0 h3 h2 hQ

/-- The second call: the MAC into `out`. -/
theorem fin2_ok {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h0 : s.gpr .r3 = inn s₀) (h3 : s.gpr .r6 = scr s₀) (h2 : s.gpr .r5 = mac s₀)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (finW s₀ (mac s₀) ++ [below s₀.sp 48]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (∀ m, Repr s.mem (inn s₀) m → s.gpr .r4 = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (mac s₀) 32 = Spec.Sha256.hash m) → Q s') :
    WP isa sha256Finalize s Q :=
  fin_ok hp hs hp.i_m (hp.m_s.sub_right (sub160 s₀)) hs.m ⟨macR s₀, by simp, 0, by simp, by simp⟩
    hrd hwr hsp h0 h3 h2 hQ

/-! ## Saving `r23`, `r24`, `r25` and the outer hash value -/

/-- The memory after saving our caller's `r23` in `scratch[240..248)` and `r24`
and `r25` in `scratch[160..176)`. -/
abbrev svMem (s₀ : State) : Mem :=
  ((s₀.mem.writeW (scr s₀ + BitVec.ofNat 64 240) (s₀.gpr .r23)).writeW (scr s₀ + BitVec.ofNat 64 160)
    (s₀.gpr .r24)).writeW (scr s₀ + BitVec.ofNat 64 168) (s₀.gpr .r25)

/-- After the prologue: our caller's `r23`, `r24` and `r25` are saved, and
the outer hash value's bytes are in `scratch[208..240)`. -/
structure Saved (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r3 : s.gpr .r3 = inn s₀
  r6 : s.gpr .r6 = scr s₀
  r23 : s.gpr .r23 = mac s₀
  r24 : s.gpr .r24 = inn s₀
  r25 : s.gpr .r25 = scr s₀
  r4 : s.gpr .r4 = s₀.gpr .r5
  r5 : s.gpr .r5 = scr s₀ + 176
  cs : ∀ r ∈ preserved, r ≠ .r23 → r ≠ .r24 → r ≠ .r25 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes (svMem s₀) (scr s₀ + BitVec.ofNat 64 208) (bytesAt s₀.mem (out s₀) 32)

theorem not_pres {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r8 :=
  (by decide : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r8) r hr

theorem svMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (svMem s₀) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))

theorem svMem_out {s₀ : State} (hp : Pre s₀) :
    bytesAt (svMem s₀) (out s₀) 32 = bytesAt s₀.mem (out s₀) 32 :=
  Proof.Sha256.Stream.bytesAt_congr fun i hi =>
    frame_bytes (svMem_frame s₀) (R := outR s₀) (by simpa using hp.o_s) (by simp) (show i < 96 by omega)

/-- Everything the prologue writes is in the scratch space. -/
theorem Saved.frame {s₀ s : State} (h : Saved s₀ s) : Frame [scR s₀] s₀.mem s.mem := by
  rw [h.mem]
  refine (svMem_frame s₀).trans (writeBytes_frame _ _ _ ?_)
  rw [bytesAt_length]; exact contains_offset (by omega) (by omega)

theorem Saved.sv_eq {s₀ s : State} (h : Saved s₀ s) {o : Nat}
    (ho : (160 ≤ o ∧ o + 8 ≤ 176) ∨ (240 ≤ o ∧ o + 8 ≤ 248)) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 = (svMem s₀).readW (scr s₀ + BitVec.ofNat 64 o) 64 := by
  rw [h.mem]
  refine (writeBytes_frame (R := ⟨scr s₀ + BitVec.ofNat 64 208, 32⟩) _ _ _
    (by rw [bytesAt_length]; exact Region.contains_self _ _)).readW (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton]; rintro r rfl
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂
  have : (BitVec.ofNat 64 o).toNat = o := toNat_ofNat_lt (by omega)
  bv_omega

theorem Saved.sv23 {s₀ s : State} (h : Saved s₀ s) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 240) 64 = s₀.gpr .r23 := by
  rw [h.sv_eq (.inr ⟨le_rfl, by omega⟩), svMem, readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    readW_writeW_save _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]

theorem Saved.sv24 {s₀ s : State} (h : Saved s₀ s) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 160) 64 = s₀.gpr .r24 := by
  rw [h.sv_eq (.inl ⟨le_rfl, by omega⟩), svMem, readW_writeW_save _ _ _ (by omega) (by omega) (by omega),
    Mem.readW_writeW_self64]

theorem Saved.sv25 {s₀ s : State} (h : Saved s₀ s) :
    s.mem.readW (scr s₀ + BitVec.ofNat 64 168) 64 = s₀.gpr .r25 := by
  rw [h.sv_eq (.inl ⟨by omega, by omega⟩), svMem, Mem.readW_writeW_self64]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (([.store .d .r23 .r7 240, .store .d .r24 .r7 160, .store .d .r25 .r7 168,
        mov .r23 .r6, mov .r24 .r3, mov .r25 .r7] : List Instr) ++ saveOuter ++
        ([mov .r4 .r5, .addi .r5 .r7 176, mov .r6 .r7] : List Instr))) s₀ (Saved s₀) := by
  unfold saveOuter
  have h0 : out s₀ + BitVec.ofNat 64 0 = out s₀ := by simp
  simp only [List.cons_append, List.nil_append]
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 240) (by decide) ⟨by omega, by omega⟩ rfl
    ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩ fun sa ua => ?_
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 160) (by decide) ⟨by omega, by omega⟩ (by rw [ua.gpr])
    ⟨scR s₀, by simp [ua.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun sb ub => ?_
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 168) (by decide) ⟨by omega, by omega⟩ (by rw [ub.gpr, ua.gpr])
    ⟨scR s₀, by simp [ub.wr, ua.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun sc uc => ?_
  refine wp_mov fun s₀' u₀ => wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => ?_
  have g : sc.gpr = s₀.gpr := by rw [uc.gpr, ub.gpr, ua.gpr]
  have e1 : s₂.gpr .r4 = out s₀ := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), u₀.other _ (by decide), g]
  have e3 : s₂.gpr .r7 = scr s₀ := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), u₀.other _ (by decide), g]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, u₀.rd, uc.rd, ub.rd, ua.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, u₀.wr, uc.wr, ub.wr, ua.wr]
  have m₂ : s₂.mem = svMem s₀ := by
    rw [u₂.mem, u₁.mem, u₀.mem, uc.mem, ub.gpr, ua.gpr, ub.mem, ua.gpr, ua.mem]
  have k₂ : ∀ r, r ≠ .r23 → r ≠ .r24 → r ≠ .r25 → s₂.gpr r = s₀.gpr r := fun r a b c => by
    rw [u₂.other _ c, u₁.other _ b, u₀.other _ a, g]
  refine copy32_ok (by decide) (by decide) (by decide) (by decide) 0 208 8 ⟨rfl, rfl⟩ ⟨by omega, by omega⟩ _ s₂ _
    (fun k hk => ?_) (fun k hk => ?_) ?_
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => wp_mov fun s₄ u₄ => wp_addi (imm := 176) (by decide) (by omega) fun s₅ u₅ =>
      wp_mov fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr h23 h24 h25 => ?_, ?_, ?_⟩
  · rw [e1, h0, rd₂, wr₂]
    exact ⟨outR s₀, by simp [hp.rd], contains_offset (by omega) (by omega)⟩
  · rw [e3, wr₂]
    refine ⟨scR s₀, by simp [hp.wr], ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact contains_offset (by omega) (by omega)
  · rw [e1, e3, h0]
    exact hp.o_s.sep (a := out s₀) (n := 32) (by simp [Region.Contains]) (contains_offset (by omega) (by omega))
  · rw [u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂]
  · rw [u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      k₂ _ (by decide) (by decide) (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), e3]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), u₀.gpr, g]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      u₂.other _ (by decide), u₁.gpr, u₀.other _ (by decide), g]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      u₂.gpr, u₁.other _ (by decide), u₀.other _ (by decide), g]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide),
      k₂ _ (by decide) (by decide) (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide), e3]; rfl
  · have := not_pres hr
    rw [u₆.other _ this.2.2.2.1, u₅.other _ this.2.2.1, u₄.other _ this.2.1, g₃ _ this.2.2.2.2,
      k₂ _ h23 h24 h25]
  · rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, u₀.sp, uc.sp, ub.sp, ua.sp]
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃, m₂, e1, e3, h0]
    exact congrArg _ (svMem_out hp)

/-! ## Loading the outer hash value and the inner digest -/

/-- After the middle block, from `s`: the inner state holds the hash value from
`scratch[208..240)` and, in its buffer, the digest from `scratch[176..208)`. -/
structure Loaded (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  r3 : s'.gpr .r3 = inn s₀
  r6 : s'.gpr .r6 = scr s₀
  r4 : s'.gpr .r4 = BitVec.ofNat 64 (64 + 32)
  r5 : s'.gpr .r5 = mac s₀
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  state : stateAt s'.mem (inn s₀) = stateAt s.mem (scr s₀ + BitVec.ofNat 64 208)
  buf : bytesAt s'.mem (inn s₀ + 32) 32 = bytesAt s.mem (scr s₀ + 176) 32
  frame : Frame [inR s₀] s.mem s'.mem

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hwr : s.wr = s₀.wr)
    (h23 : s.gpr .r23 = mac s₀) (h25 : s.gpr .r24 = inn s₀) (h26 : s.gpr .r25 = scr s₀) :
    WP isa (.block (loadOuter ++ [mov .r3 .r24, .li .r4 96, mov .r5 .r23, mov .r6 .r25]))
      s (Loaded s₀ s) := by
  unfold loadOuter
  rw [List.append_assoc]
  have hin : ∀ {o k : Nat}, o + k ≤ 248 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨scR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩
  have hout : ∀ {o k : Nat}, o + k ≤ 96 → InRegions s.wr (inn s₀ + BitVec.ofNat 64 o) k :=
    fun h => ⟨inR s₀, by simp [hwr, hp.wr], contains_offset h (by omega)⟩
  have add : ∀ (p : Addr) (a b : Nat), p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) :=
    fun p a b => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine copy32_ok (src := .r25) (dst := .r24) (by decide) (by decide) (by decide) (by decide) 208 0 8 ⟨rfl, rfl⟩
    ⟨by omega, by omega⟩ _ s _ ?_ ?_ ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · intro k hk; rw [h26, add]; exact hin (by omega)
  · intro k hk; rw [h25, add]; exact hout (by omega)
  · rw [h26, h25]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  have e₁ : s₁.gpr .r25 = scr s₀ := by rw [g₁ _ (by decide), h26]
  have d₁ : s₁.gpr .r24 = inn s₀ := by rw [g₁ _ (by decide), h25]
  refine copy64_ok (src := .r25) (dst := .r24) (by decide) (by decide) (by decide) (by decide) 176 32 4 ⟨rfl, rfl⟩
    ⟨by omega, by omega⟩ _ s₁ _ ?_ ?_ ?_ fun s₂ g₂ rd₂ wr₂ sp₂ m₂ =>
      wp_mov fun s₃ u₃ => wp_li (imm := 96) (by omega) fun s₄ u₄ => wp_mov fun s₅ u₅ =>
        wp_mov fun s₆ u₆ => WP.block_nil ?_
  · intro k hk; rw [e₁, add, rd₁, wr₁]; exact hin (by omega)
  · intro k hk; rw [d₁, add, wr₁]; exact hout (by omega)
  · rw [e₁, d₁]
    exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  rw [h26, h25, show inn s₀ + BitVec.ofNat 64 0 = inn s₀ by simp] at m₁
  rw [e₁, d₁] at m₂
  have c₀ : (inR s₀).Contains (inn s₀) 32 := by simp [Region.Contains]
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have k₂ : ∀ r, r ≠ .r8 → s₂.gpr r = s.gpr r := fun r h => by rw [g₂ r h, g₁ r h]
  have hbuf : bytesAt s₂.mem (inn s₀ + 32) 32 = bytesAt s.mem (scr s₀ + 176) 32 := by
    rw [m₂, show inn s₀ + 32 = inn s₀ + BitVec.ofNat 64 32 from rfl]
    have := bytesAt_writeBytes_self s₁.mem (inn s₀ + BitVec.ofNat 64 32)
      (bytesAt s₁.mem (scr s₀ + BitVec.ofNat 64 176) (8 * 4)) (by simp [bytesAt])
    rw [bytesAt_length] at this
    rw [this, m₁, bytesAt_writeBytes_sep]
    · rfl
    · rw [bytesAt_length]
      exact hp.i_s.symm.sep (contains_offset (by omega) (by omega)) c₀
    · omega
  have hst : stateAt s₂.mem (inn s₀) = stateAt s.mem (scr s₀ + BitVec.ofNat 64 208) := by
    refine stateAt_eq_of_bytes fun i hi => ?_
    rw [m₂, writeBytes_other _ _ _ (by rw [bytesAt_length]; bv_omega), m₁,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; omega) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ (by omega)]
  have hfr : Frame [inR s₀] s.mem s₂.mem := by
    rw [m₂, m₁]
    refine (writeBytes_frame (R := inR s₀) _ _ _ ?_).trans (writeBytes_frame (R := inR s₀) _ _ _ ?_)
    · rw [bytesAt_length]; exact c₀
    · rw [bytesAt_length]; exact contains_offset (by omega) (by omega)
  refine ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁],
    ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁],
    by rw [hm, hst], by rw [hm, hbuf], by rw [hm]; exact hfr⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, k₂ _ (by decide), h25]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), h26]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), k₂ _ (by decide), h23]
  · have := not_pres hr
    rw [u₆.other _ this.2.2.2.1, u₅.other _ this.2.2.1, u₄.other _ this.2.1, u₃.other _ this.1,
      k₂ _ this.2.2.2.2]

/-! ## Correctness -/

/-- The bytes of `scratch` the calls of `vg_sha256_finalize` leave alone: our
caller's registers and the outer hash value. -/
abbrev Kept (o : Nat) : Prop := (160 ≤ o ∧ o < 176) ∨ (208 ≤ o ∧ o < 248)

/-- A call of `vg_sha256_finalize` into `d` writes outside the bytes `Kept`. -/
theorem not_finW {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {d : Addr}
    (hd : ∀ o, Kept o → Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ ⟨d, 32⟩) {o : Nat} (ho : Kept o) :
    ∀ r ∈ finW s₀ d ++ [below s₀.sp 48], (⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ : Region).Disjoint r := by
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ (scR s₀) := sub_offset (by omega) (by omega)
  have ht : (BitVec.ofNat 64 o).toNat = o := toNat_ofNat_lt (by omega)
  intro r hr
  simp only [finW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.i_s.symm.sub_left hsub
  · exact hd o ho
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · exact hs.s.symm.sub_left hsub

theorem kept_176 (s₀ : State) : ∀ o, Kept o →
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ ⟨scr s₀ + 176, 32⟩ := by
  intro o ho a h₁ h₂
  have ht : (BitVec.ofNat 64 o).toNat = o := toNat_ofNat_lt (by omega)
  simp only [Region.Contains] at h₁ h₂; bv_omega

theorem kept_mac {s₀ : State} (hp : Pre s₀) : ∀ o, Kept o →
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ ⟨mac s₀, 32⟩ := fun o ho =>
  hp.m_s.symm.sub_left (sub_offset (by omega) (by omega))

/-- A byte `Kept` survives a call. -/
theorem kept {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {d : Addr}
    (hd : ∀ o, Kept o → Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ ⟨d, 32⟩) {m m' : Mem}
    (hf : Frame (finW s₀ d ++ [below s₀.sp 48]) m m') {o : Nat} (ho : Kept o) :
    m' (scr s₀ + BitVec.ofNat 64 o) = m (scr s₀ + BitVec.ofNat 64 o) := by
  have := frame_bytes hf (not_finW hp hs hd ho) Nat.one_le_two_pow (i := 0) Nat.one_pos
  simpa using this

/-- A byte of `scratch` survives loading the inner state. -/
theorem kept_load {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [inR s₀] m m') {o : Nat}
    (ho : o < 248) : m' (scr s₀ + BitVec.ofNat 64 o) = m (scr s₀ + BitVec.ofNat 64 o) := by
  have hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩ (scR s₀) := sub_offset (by omega) (by omega)
  have := frame_bytes hf (R := ⟨scr s₀ + BitVec.ofNat 64 o, 1⟩)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left hsub) Nat.one_le_two_pow
    (i := 0) Nat.one_pos
  simpa using this

/-- A saved register survives the calls and the load. -/
theorem sv_kept {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) {m₁ m₂ m₃ m₄ : Mem}
    (f₂ : Frame (finW s₀ (scr s₀ + 176) ++ [below s₀.sp 48]) m₁ m₂) (f₃ : Frame [inR s₀] m₂ m₃)
    (f₄ : Frame (finW s₀ (mac s₀) ++ [below s₀.sp 48]) m₃ m₄) {o : Nat} (ho : o = 160 ∨ o = 168 ∨ o = 240) :
    m₄.readW (scr s₀ + BitVec.ofNat 64 o) 64 = m₁.readW (scr s₀ + BitVec.ofNat 64 o) 64 := by
  simp only [Mem.readW]
  refine congrArg _ (Mem.read_congr fun i hi => ?_)
  have e : scr s₀ + BitVec.ofNat 64 o + BitVec.ofNat 64 i = scr s₀ + BitVec.ofNat 64 (o + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hi' : i < 8 := hi
  rw [e, kept hp hs (kept_mac hp) f₄ (by omega), kept_load hp f₃ (by omega),
    kept hp hs (kept_176 s₀) f₂ (by omega)]

theorem sub48 (sp : Addr) : Region.Sub ⟨sp - 48, 48⟩ (below sp 96) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- `finalize` without its frame. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa finalizeMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Hmac.finalizeSha256PPC64LE.post s₀ s' := by
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (fin1_ok hp hs h₁.rd h₁.wr h₁.sp h₁.r3 h₁.r6 h₁.r5
    fun s₂ rd₂ wr₂ sp₂ fr₂ cs₂ post₂ => ?_)
  have r23₂ : s₂.gpr .r23 = mac s₀ := by rw [cs₂ _ (by decide), h₁.r23]
  have r24₂ : s₂.gpr .r24 = inn s₀ := by rw [cs₂ _ (by decide), h₁.r24]
  have r25₂ : s₂.gpr .r25 = scr s₀ := by rw [cs₂ _ (by decide), h₁.r25]
  refine WP.seq (WP.mono (load_ok hp (s := s₂) (wr₂.trans h₁.wr) r23₂ r24₂ r25₂) fun s₃ h₃ => ?_)
  refine WP.seq (fin2_ok hp hs (h₃.rd.trans (rd₂.trans h₁.rd)) (h₃.wr.trans (wr₂.trans h₁.wr))
    (h₃.sp.trans (sp₂.trans h₁.sp)) h₃.r3 h₃.r6 h₃.r5
    fun s₄ rd₄ wr₄ sp₄ fr₄ cs₄ post₄ => ?_)
  -- Restoring `r23`, `r24` and `r25`.
  have r25₄ : s₄.gpr .r25 = scr s₀ := by
    rw [cs₄ _ (by decide), h₃.cs _ (by decide), r25₂]
  have hin : ∀ o, o + 8 ≤ 248 → InRegions (s₄.rd ++ s₄.wr) (scr s₀ + BitVec.ofNat 64 o) 8 := fun o h =>
    ⟨scR s₀, by simp [wr₄, h₃.wr, wr₂, h₁.wr, hp.wr], contains_offset h (by omega)⟩
  have sv : ∀ o, o = 160 ∨ o = 168 ∨ o = 240 → s₄.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 =
      s₁.mem.readW (scr s₀ + BitVec.ofNat 64 o) 64 :=
    fun o ho => sv_kept hp hs fr₂ h₃.frame fr₄ ho
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 240) (by decide) ⟨by omega, by omega⟩ (by rw [r25₄])
    (hin 240 (by omega)) fun s₅ u₅ => ?_
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 160) (by decide) ⟨by omega, by omega⟩
    (by rw [u₅.other _ (by decide), r25₄])
    (by rw [u₅.rd, u₅.wr]; exact hin 160 (by omega)) fun s₆ u₆ => ?_
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 168) (by decide) ⟨by omega, by omega⟩
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), r25₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr]; exact hin 168 (by omega)) fun s₇ u₇ => WP.block_nil
      ⟨fun r hr => ?_, by rw [u₇.sp, u₆.sp, u₅.sp, sp₄, h₃.sp, sp₂, h₁.sp], ?_⟩
  · by_cases h25 : r = .r25
    · subst h25; rw [u₇.gpr, u₆.mem, u₅.mem, sv _ (.inr (.inl rfl)), h₁.sv25]
    by_cases h24 : r = .r24
    · subst h24; rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, sv _ (.inl rfl), h₁.sv24]
    by_cases h23 : r = .r23
    · subst h23; rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, sv _ (.inr (.inr rfl)),
        h₁.sv23]
    rw [u₇.other _ h25, u₆.other _ h24, u₅.other _ h23, cs₄ _ hr, h₃.cs _ hr, cs₂ _ hr,
      h₁.cs _ hr h23 h24 h25]
  · intro k0 text hk _ hin hcnt hout
    -- The inner digest.
    have hin₁ : Repr s₁.mem (inn s₀) (xorPad k0 ipad ++ text) :=
      Proof.Sha256.Stream.repr_congr (fun i hi => frame_bytes h₁.frame (R := inR s₀)
        (by simpa using hp.i_s) (by simp) hi) hin
    have hd := post₂ _ hin₁ (by rw [h₁.r4, hcnt, List.length_append, xorPad_length, hk])
    -- The outer state.
    have hst : stateAt s₃.mem (inn s₀) = Spec.Sha256.compressList Spec.Sha256.H0 (xorPad k0 opad) 1 := by
      rw [h₃.state]
      have e : stateAt s₂.mem (scr s₀ + BitVec.ofNat 64 208) = stateAt s₀.mem (out s₀) := by
        refine stateAt_eq_of_bytes fun i hi => ?_
        rw [show scr s₀ + BitVec.ofNat 64 208 + BitVec.ofNat 64 i = scr s₀ + BitVec.ofNat 64 (208 + i) by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add],
          kept hp hs (kept_176 s₀) fr₂ (by omega), BitVec.ofNat_add,
          ← BitVec.add_assoc, h₁.mem,
          writeBytes_at _ _ _ (by rw [bytesAt_length]; omega) (by rw [bytesAt_length]; omega),
          bytesAt_getD' _ _ (by omega)]
      rw [e, hout.1, xorPad_length, hk]
    have hrepr := repr_outer hk (by rw [bytesAt_length]) hst h₃.buf
    have := post₄ _ hrepr (by rw [h₃.r4, List.length_append, xorPad_length, hk, bytesAt_length])
    rw [hd] at this
    rw [u₇.mem, u₆.mem, u₅.mem]
    simpa [hmacBlockKey, sha256] using this

/-- The state `finalizeMain` starts in: the link register moved to `r0`,
then pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack₀ s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Hmac.finalizeSha256PPC64LE.post s₀ s' := by
  have hsp := hs.sp96
  have hb : Region.Sub (below (s₀.sp - 48) 48) (below s₀.sp 96) := below_body s₀.sp 48
  have hf : Region.Sub ⟨s₀.sp - 48, 48⟩ (below s₀.sp 96) := sub48 s₀.sp
  have hsi : Stack (inner s₀) :=
    ⟨by show 48 ≤ (s₀.sp - 48).toNat; bv_omega, hs.i.sub_left hb, hs.o.sub_left hb, hs.m.sub_left hb,
      hs.s.sub_left hb⟩
  refine WP.seq (cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by show 48 ≤ s₀.sp.toNat; omega) (fun R hR => ?_)
    (WP.mono (correctMain (s₀ := inner s₀) ⟨hp.rd, hp.wr, hp.i_o, hp.i_m, hp.i_s, hp.o_m, hp.o_s, hp.m_s⟩ hsi)
      fun s' ⟨hk, _, hpost⟩ => ?_)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (hs.i.sub_left hf).sub_left (frame_sub _)
    · exact (hs.m.sub_left hf).sub_left (frame_sub _)
    · exact (hs.s.sub_left hf).sub_left (frame_sub _)
  · refine cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, fun k0 text hk hlen hin hcnt hout => ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have c : ∀ p : Addr, Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, 96⟩ → ∀ l,
          Repr s₀.mem p l → Repr (inner s₀).mem p l := fun p hd l h =>
        Proof.Sha256.Stream.repr_congr (fun i hi => write_frame_bytes (R := ⟨p, 96⟩) hd (show 96 < 2 ^ 64 by omega) hi) h
      have := hpost k0 text hk hlen (c _ (hs.i.sub_left hf) _ hin) hcnt (c _ (hs.o.sub_left hf) _ hout)
      exact this

/-! ## `Verified` -/

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Hmac.finalizeSha256PPC64LE.pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x5000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 96⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x5000, 32⟩, ⟨0x3000, 248⟩]

theorem finalize_verified : Verified PPC64LE.target finalize Proof.Hmac.finalizeSha256PPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Hmac.PPC64LE.Finalize
