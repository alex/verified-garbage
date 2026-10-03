import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_finish`

The code copies the chaining value to `out`, saves `x19` and `x30` in the
scratch buffer, computes the number of bytes held back, and calls
`vg_cmac_aes_finalize` with the state as its key and `out` as its state: its
result is the MAC of the message the state represents (`repr_finish`). The
code before the call and the restore after it are constant time by the taint
analysis, and the call by its own proof (`fin_rel`), its arguments pinned by
`HMid`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.CmacAes.Stream.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 readW_writeW_other agree_of)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.Cmac.Stream (held held_le)

/-- The precondition, by name: the state `St`, `out` (`O`), the scratch
buffer `S` and the rounds `R`. -/
structure HPre (s₀ : State) (St O S : Addr) (R : Nat) : Prop where
  x0 : s₀.gpr .x0 = St
  x3 : s₀.gpr .x3 = O
  x4 : s₀.gpr .x4 = S
  x1 : (s₀.gpr .x1).toNat = R
  rd : s₀.rd = []
  wr : s₀.wr = [⟨St, 304⟩, ⟨O, 16⟩, ⟨S, 2304⟩]
  st_o : (⟨St, 304⟩ : Region).Disjoint ⟨O, 16⟩
  st_s : (⟨St, 304⟩ : Region).Disjoint ⟨S, 2304⟩
  o_s : (⟨O, 16⟩ : Region).Disjoint ⟨S, 2304⟩
  wSt : St.toNat + 304 ≤ 2 ^ 64
  wO : O.toNat + 16 ≤ 2 ^ 64
  wS : S.toNat + 2304 ≤ 2 ^ 64
  rounds : R = 10 ∨ R = 12 ∨ R = 14

theorem HPre.of {s₀ : State} (h : finishAArch64.pre s₀) :
    HPre s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-! ## Before the call -/

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def copyMem (m : Mem) (o p : Addr) : Mem :=
  let m₁ := m.writeW o (m.readW p 64)
  m₁.writeW (o + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 16⟩] m (copyMem m o p) :=
  Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) {o p : Addr} (h : (⟨o, 16⟩ : Region).Disjoint ⟨p, 16⟩) :
    Spec.Aes.bytesAt (copyMem m o p) o 16 = Spec.Aes.bytesAt m p 16 := by
  have g : Frame [⟨o, 8⟩] m (m.writeW o (m.readW p 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [copyMem, Proof.Cmac.bytesAt_store2,
    g.readW (r := ⟨p + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.sub_left (Region.sub_prefix (by decide))).sub_right
          (Offset.sub_base p (d := 8) (n := 8) (k := 16) (by decide)) |>.symm) (by decide),
    Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]

/-- The memory after `finishPre`. -/
def finMem (s : State) (St O S : Addr) : Mem :=
  ((copyMem s.mem O (St + BitVec.ofNat 64 272)).writeW (S + BitVec.ofNat 64 2176) (s.gpr .x19)).writeW
    (S + BitVec.ofNat 64 2184) (s.gpr .x30)

theorem finishPre_ok {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    ∃ s₁, runBlock isa finishPre s₀ = some s₁ ∧ s₁.gpr .x0 = St ∧ s₁.gpr .x1 = s₀.gpr .x1 ∧
      s₁.gpr .x2 = O ∧ s₁.gpr .x3 = St + BitVec.ofNat 64 288 ∧ s₁.gpr .x4 = s₀.gpr .x2 ∧
      s₁.gpr .x5 = S ∧ s₁.gpr .x19 = S ∧ (∀ r ∈ preserved, r ≠ .x19 → s₁.gpr r = s₀.gpr r) ∧
      s₁.sp = s₀.sp ∧ s₁.mem = finMem s₀ St O S ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hw := hp.wSt
  have inSt (d : Nat) (hd : d + 8 ≤ 304) : InRegions (s₀.rd ++ s₀.wr) (St + BitVec.ofNat 64 d) 8 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨St, 304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  have inO (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₀.wr (O + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨O, 16⟩, by simp, Offset.contains_base _ hd (by have := hp.wO; omega)⟩
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions s₀.wr (S + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr]; exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by have := hp.wS; omega)⟩
  refine ⟨_, by
    simp (config := {decide := true}) only [finishPre, mov, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write,
      rd_write, wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      hp.x0, hp.x3, hp.x4, inSt 272 (by decide), inSt 280 (by decide), inO 0 (by decide),
      inO 8 (by decide), inS 2176 (by decide), inS 2184 (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, hp.x0], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r hr h19 => ?_, rfl, ?_, rfl, rfl⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
  · simp only [mem_write, finMem, copyMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq, k0, Offset.add_add,
      Nat.reduceAdd]

/-- Storing two words in the slots at `S + 2176`. -/
theorem slots_frame (m : Mem) (S : Addr) (a b : BitVec 64) :
    Frame [⟨S + BitVec.ofNat 64 2176, 16⟩] m
      ((m.writeW (S + BitVec.ofNat 64 2176) a).writeW (S + BitVec.ofNat 64 2184) b) := by
  rw [(Offset.add_add_eq S (a := 2176) (b := 8) (c := 2184) rfl).symm]
  exact Proof.Cmac.frame_store2 _ _ _

theorem finMem_frame (s : State) (St O S : Addr) :
    Frame [⟨O, 16⟩, ⟨S + BitVec.ofNat 64 2176, 16⟩] s.mem (finMem s St O S) :=
  ((copyMem_frame _ _ _).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp only [List.mem_cons, true_or]).trans
  ((slots_frame _ _ _ _).mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem finMem_slots (s : State) (St O S : Addr) :
    (finMem s St O S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .x19 ∧
      (finMem s St O S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .x30 :=
  ⟨by rw [finMem, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64],
    by rw [finMem, Mem.readW_writeW_self64]⟩

/-- What the code before the call leaves. -/
structure HMid (s₀ : State) (St O S : Addr) (R : Nat) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 64 288) S (held (s₀.gpr .x2).toNat) R
  mem : s.mem = finMem s₀ St O S
  x19 : s.gpr .x19 = S
  saved : ∀ r ∈ preserved, r ≠ .x19 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.fargs {s₀ s : State} {St O S : Addr} {R L : Nat} (hp : HPre s₀ St O S R) (hL : L ≤ 16)
    (x0 : s.gpr .x0 = St) (x1 : s.gpr .x1 = s₀.gpr .x1) (x2 : s.gpr .x2 = O)
    (x3 : s.gpr .x3 = St + BitVec.ofNat 64 288) (x4 : s.gpr .x4 = BitVec.ofNat 64 L)
    (x5 : s.gpr .x5 = S) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 64 288) S L R := by
  have hw := hp.wSt
  have pSt : Region.Sub ⟨St + BitVec.ofNat 64 288, L⟩ ⟨St, 304⟩ := Offset.sub_base St (by omega)
  exact
  { x0 := x0, x2 := x2, x3 := x3, x4 := x4, x5 := x5
    x1 := by rw [x1]; exact ofNat_toNat_eq hp.x1
    rounds := hp.rounds, len := hL
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := (hp.st_s.sub_left pSt).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    wrapK := by omega
    wrapSt := hp.wO
    wrapP := by rw [toNat_add_lt St hw (by decide)]; omega
    wrapS := by have := hp.wS; omega
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨St, 304⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨St, 304⟩, by simp, 288, rfl, by simp; omega⟩
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨O, 16⟩, by simp, 0, by simp, by simp⟩
      · exact ⟨⟨S, 2304⟩, by simp, 0, by simp, by simp⟩ }

theorem lastLen_ok (s : State) {c : BitVec 64} (h4 : s.gpr .x4 = c) (hc : c ≠ 0) :
    ∃ s', runBlock isa [.subImm .x .x4 .x4 1, .movz .x .x9 15 0, .logic .and .x .x4 .x4 .x9,
        .addImm .x .x4 .x4 1] s = some s' ∧ s'.gpr .x4 = BitVec.ofNat 64 (held c.toNat) ∧
      (∀ r, r ≠ .x4 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl, rfl, rfl⟩
  simp only [gpr_write, ite_true, BitVec.setWidth_eq, mz15, h4]
  exact held_bv c hc

theorem finPre_wp {s₀ : State} {St O S : Addr} {R : Nat} (hp : HPre s₀ St O S R) :
    WP isa finPre s₀ (HMid s₀ St O S R) := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x19₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ := finishPre_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hc := (s₀.gpr .x2).isLt
  have h2 : s₀.gpr .x2 = BitVec.ofNat 64 (s₀.gpr .x2).toNat := ofNat_toNat_eq rfl
  by_cases h0 : (s₀.gpr .x2).toNat = 0
  · refine WP.ite true (by rw [eval_zero hc (by rw [x4₁]; exact h2), h0]; rfl)
      (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨hp.fargs (held_le _) x0₁ x1₁ x2₁ x3₁ ?_ x5₁ rd₁ wr₁, m₁, x19₁, sv₁, sp₁, rd₁, wr₁⟩
    rw [x4₁, h2, h0]; rfl
  · refine WP.ite false (by rw [eval_zero hc (by rw [x4₁]; exact h2)]; simp [h0])
      (fun h => by cases h) fun _ => ?_
    have hne : s₀.gpr .x2 ≠ 0 := fun e => h0 (by rw [e]; rfl)
    obtain ⟨s₂, run₂, x4₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := lastLen_ok s₁ x4₁ hne
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    have hc : ∀ r ∈ preserved, r ≠ .x4 ∧ r ≠ .x9 := by decide
    refine ⟨hp.fargs (held_le _) (by rw [g₂ _ (by decide) (by decide), x0₁])
      (by rw [g₂ _ (by decide) (by decide), x1₁]) (by rw [g₂ _ (by decide) (by decide), x2₁])
      (by rw [g₂ _ (by decide) (by decide), x3₁]) x4₂ (by rw [g₂ _ (by decide) (by decide), x5₁])
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]), by rw [m₂, m₁],
      by rw [g₂ _ (by decide) (by decide), x19₁],
      fun r hr h19 => by rw [g₂ r (hc r hr).1 (hc r hr).2, sv₁ r hr h19], by rw [sp₂, sp₁], by rw [rd₂, rd₁],
      by rw [wr₂, wr₁]⟩

/-! ## After the call -/

theorem finishPost_ok (s : State) {B : Addr} (hb : s.gpr .x19 = B)
    (r₁ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2184) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 2176) 8) :
    ∃ s', runBlock isa finishPost s = some s' ∧
      s'.gpr .x30 = s.mem.readW (B + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .x19 = s.mem.readW (B + BitVec.ofNat 64 2176) 64 ∧
      (∀ r, r ≠ .x19 → r ≠ .x30 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [finishPost, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write, wr_write, ite_true, ite_false,
      Option.bind_some, Option.map_some, hb, r₁, r₂]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write, Mem.readW], by simp [gpr_write, Mem.readW],
    fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, rfl⟩

/-! ## The whole function -/

theorem finish_wp (v : Ctr32Impl) {s₀ : State} (h0 : finishAArch64.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => GprAbi s₀ s' ∧ finishAArch64.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .x0 = St at hp
  generalize s₀.gpr .x3 = O at hp
  generalize s₀.gpr .x4 = S at hp
  generalize (s₀.gpr .x1).toNat = R at hp
  have hw := hp.wSt
  have sw := hp.wS
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_call v _ h₁.args) fun s₂ h₂ => ?_)
  have x19₂ : s₂.gpr .x19 = S := by rw [h₂.saved _ (by simp [preserved]) (by decide), h₁.x19]
  have inS (d : Nat) (hd : d + 8 ≤ 2304) : InRegions (s₂.rd ++ s₂.wr) (S + BitVec.ofNat 64 d) 8 := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 2304⟩, by simp, Offset.contains_base _ hd (by omega)⟩
  obtain ⟨s₃, run₃, x30₃, x19₃, g₃, sp₃, m₃⟩ := finishPost_ok s₂ x19₂ (inS 2184 (by decide))
    (inS 2176 (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  -- The slots, which the call does not write.
  have slots (d : Nat) (h₁' : 2176 ≤ d) (h₂' : d + 8 ≤ 2304) :
      s₂.mem.readW (S + BitVec.ofNat 64 d) 64 = s₁.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    refine h₂.frame.readW (r := ⟨S + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.o_s.symm.sub_left (Offset.sub_base S h₂')
    · exact Offset.disjoint_base _ (by omega) (by omega)
  obtain ⟨sl19, sl30⟩ := finMem_slots s₀ St O S
  refine ⟨⟨fun r hr => ?_, by rw [sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h19 : r = .x19
    · subst h19; rw [x19₃, slots 2176 (by decide) (by decide), h₁.mem, sl19]
    by_cases h30 : r = .x30
    · subst h30; rw [x30₃, slots 2184 (by decide) (by decide), h₁.mem, sl30]
    rw [g₃ r h19 h30, h₂.saved r hr h30, h₁.saved r hr h19]
  · intro key msg hr hR hc hlen
    rw [hp.x0] at hr
    rw [Proof.Cmac.Stream.repr_iff] at hr
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := hr
    have hn : (s₀.gpr .x2).toNat = msg.length := by rw [hc, toNat_ofNat hlen]
    rw [hp.x3, m₃]
    have hR' : R = Spec.Aes.rounds (key.length / 4) := by rw [← hp.x1]; exact hR
    -- The state is unchanged before the call.
    have fSt : ∀ {d n : Nat}, d + n ≤ 304 → Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 d) n =
        Spec.Aes.bytesAt s₀.mem (St + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [h₁.mem]
      exact Proof.Cmac.bytesAt_frame (finMem_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_o.sub_left (Offset.sub_base St hd)
        · exact (hp.st_s.sub_left (Offset.sub_base St hd)).sub_right (Offset.sub_base S (by decide)))
        (by omega)
    have hsch : Spec.Aes.bytesAt s₁.mem St (16 * (R + 1)) = Spec.Aes.expandKey key := by
      have := fSt (d := 0) (n := 16 * (R + 1)) (by rcases hp.rounds with h | h | h <;> omega)
      rw [k0] at this; rw [this, hR']; exact hks
    have hciph : Spec.Cmac.aesWith R (Spec.Aes.bytesAt s₁.mem St (16 * (R + 1))) = Spec.Cmac.aes key := by
      rw [hsch, hR']; rfl
    have e₁ : Spec.Aes.bytesAt s₁.mem (St + 240) 32 = Spec.Aes.bytesAt s₀.mem (St + 240) 32 :=
      fSt (d := 240) (by decide)
    have e₂ : Spec.Aes.bytesAt s₁.mem O 16 = Spec.Aes.bytesAt s₀.mem (St + 272) 16 := by
      rw [h₁.mem, finMem, Proof.Cmac.bytesAt_frame16 (slots_frame _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.o_s.sub_right (Offset.sub_base S (by decide)))]
      exact copyMem_bytes _ (hp.st_o.symm.sub_right (Offset.sub_base St (by decide)))
    have e₃ : Spec.Aes.bytesAt s₁.mem (St + BitVec.ofNat 64 288) (held (s₀.gpr .x2).toNat) =
        Spec.Aes.bytesAt s₀.mem (St + 288) (held msg.length) := by
      rw [hn]; exact fSt (by have := held_le msg.length; omega)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish
      ((Proof.Cmac.Stream.repr_iff _ _ _ _).mpr ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩)
    have out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

theorem finish_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finishAArch64.pre s₀)
    (h0' : finishAArch64.pre s₀') (hq : finishAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat := by
    rw [q0, q1, q3, q4]; exact HPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block finishPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q5 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := HMid s₀ _ _ _ _) (F₂ := HMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix) (P := fun s₁ s₂ =>
      HMid s₀ (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat s₁ ∧
      HMid s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x4) (s₀.gpr .x1).toNat s₂)
    fun s₁ s₂ h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x4 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x4 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (fin_call v _ h.1.args) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (fin_call v _ h.2.args) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x4 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .x19 = s₀.gpr .x4 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2, h.2.2, q5]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finish_ct (v : Ctr32Impl) :
    ConstantTime isa finishAArch64.pre finishAArch64.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64
