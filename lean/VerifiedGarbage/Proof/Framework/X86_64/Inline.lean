import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Inlining verified code (x86-64)

Untrusted: everything here is checked by Lean.

The code of a verified function can be inlined into another function whose
state permits more memory. Running code from a state that permits more
(`Exec.widen`) gives the same result, and code never writes outside the
regions its state permits (`Exec.frame`). `WP.inline` combines the two with
the correctness part of the inlined function's `Verified` proof.
-/

namespace VG.X86_64

/-- Every access that `rs` permits, `rs'` permits. -/
def Covers (rs rs' : List Region) : Prop := ∀ a n, InRegions rs a n → InRegions rs' a n

/-- `s`, permitted to read `rd` and write `wr` instead. -/
def State.withRegions (s : State) (rd wr : List Region) : State := { s with rd := rd, wr := wr }

@[simp] theorem State.withRegions_gpr (s : State) (rd wr) : (s.withRegions rd wr).gpr = s.gpr := rfl
@[simp] theorem State.withRegions_mem (s : State) (rd wr) : (s.withRegions rd wr).mem = s.mem := rfl
@[simp] theorem State.withRegions_rd (s : State) (rd wr) : (s.withRegions rd wr).rd = rd := rfl
@[simp] theorem State.withRegions_wr (s : State) (rd wr) : (s.withRegions rd wr).wr = wr := rfl
@[simp] theorem State.withRegions_self (s : State) : s.withRegions s.rd s.wr = s := rfl
@[simp] theorem State.withRegions_withRegions (s : State) (rd wr rd' wr') :
    (s.withRegions rd wr).withRegions rd' wr' = s.withRegions rd' wr' := rfl

section
variable {s s' : State} {rd wr : List Region}

theorem Covers.append {rs rs' ts ts' : List Region} (h : Covers rs rs') (h' : Covers ts ts') :
    Covers (rs ++ ts) (rs' ++ ts') := by
  intro a n ⟨r, hr, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r', hr', hc'⟩ := h a n ⟨r, hr, hc⟩; exact ⟨r', List.mem_append_left _ hr', hc'⟩
  · obtain ⟨r', hr', hc'⟩ := h' a n ⟨r, hr, hc⟩; exact ⟨r', List.mem_append_right _ hr', hc'⟩

/-- Sub-regions: each region of `rs` lies at some offset within a region of `rs'`. -/
theorem Covers.of_sub {rs rs' : List Region}
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len) :
    Covers rs rs' := by
  intro a n ⟨r, hr, hc⟩
  obtain ⟨r', hr', off, hb, hl⟩ := h r hr
  refine ⟨r', hr', ?_⟩
  unfold Region.Contains at *
  rw [hb] at hc
  have : (a - r'.base).toNat ≤ (a - (r'.base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - r'.base = (a - (r'.base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by
        rw [Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

/-- A frame's push inserts its region into the writable regions of both
states. -/
theorem Covers.push {xs ys xs' ys' : List Region} (f : Region) (h : Covers (xs ++ ys) (xs' ++ ys')) :
    Covers (xs ++ f :: ys) (xs' ++ f :: ys') := fun a n hi =>
  (InRegions_append_cons.mp hi).elim (fun hc => InRegions_append_cons.mpr (.inl hc))
    fun hi => InRegions_append_cons.mpr (.inr (h a n hi))

theorem load64_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 64}
    (h : s.load64 a = some v) : (s.withRegions rd wr).load64 a = some v := by
  simp only [State.load64] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load64, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem load32_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 32}
    (h : s.load32 a = some v) : (s.withRegions rd wr).load32 a = some v := by
  simp only [State.load32] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load32, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem load8_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : Byte}
    (h : s.load8 a = some v) : (s.withRegions rd wr).load8 a = some v := by
  simp only [State.load8] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load8, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem readSrc_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {src : Src} {v : BitVec 64}
    (h : readSrc s src = some v) : readSrc (s.withRegions rd wr) src = some v := by
  cases src with
  | mem m => exact load64_widen hc h
  | _ => exact h

theorem readSrc32_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {src : Src} {v : BitVec 32}
    (h : readSrc32 s src = some v) : readSrc32 (s.withRegions rd wr) src = some v := by
  cases src with
  | mem m => exact load32_widen hc h
  | _ => exact h

theorem store64_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 64} (h : s.store64 a v = some s') :
    (s.withRegions rd wr).store64 a v = some (s'.withRegions rd wr) := by
  simp only [State.store64] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store64, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem store32_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 32} (h : s.store32 a v = some s') :
    (s.withRegions rd wr).store32 a v = some (s'.withRegions rd wr) := by
  simp only [State.store32] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store32, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem store8_widen (hc : Covers s.wr wr) {a : Addr} {v : Byte} (h : s.store8 a v = some s') :
    (s.withRegions rd wr).store8 a v = some (s'.withRegions rd wr) := by
  simp only [State.store8] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store8, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem load128_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 128}
    (h : s.load128 a = some v) : (s.withRegions rd wr).load128 a = some v := by
  simp only [State.load128] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load128, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store128_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 128} (h : s.store128 a v = some s') :
    (s.withRegions rd wr).store128 a v = some (s'.withRegions rd wr) := by
  simp only [State.store128] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store128, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem load256_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 256}
    (h : s.load256 a = some v) : (s.withRegions rd wr).load256 a = some v := by
  simp only [State.load256] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load256, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store256_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 256} (h : s.store256 a v = some s') :
    (s.withRegions rd wr).store256 a v = some (s'.withRegions rd wr) := by
  simp only [State.store256] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store256, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem load512_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 512}
    (h : s.load512 a = some v) : (s.withRegions rd wr).load512 a = some v := by
  simp only [State.load512] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load512, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store512_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 512} (h : s.store512 a v = some s') :
    (s.withRegions rd wr).store512 a v = some (s'.withRegions rd wr) := by
  simp only [State.store512] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store512, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) {i : Instr}
    (h : exec i s = some s') : exec i (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases i with
  | mov d src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec, readSrc_widen hc hv, Option.map_some]; rfl
  | mov32 d src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec, readSrc32_widen hc hv, Option.map_some]; rfl
  | movzx8 d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load8_widen hc hv]; rfl
  | store m r => exact store64_widen hw h
  | store32 m r => exact store32_widen hw h
  | store8 m r => exact store8_widen hw h
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, out, ho, rfl⟩ := h
    refine ⟨b, readSrc_widen hc hb, out, ho, ?_⟩
    split <;> rfl
  | alu32 op d src =>
    simp only [exec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, out, ho, rfl⟩ := h
    refine ⟨b, readSrc32_widen hc hb, out, ho, ?_⟩
    split <;> rfl
  | shift32 op d n =>
    simp only [exec, execShift32] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | bswap32 d => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | rorx32 d r n =>
    simp only [exec, execRorx32] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    simp only [Option.some.injEq] at h; subst h; rfl
  | andn32 d a b => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | rorx d r n =>
    simp only [exec, execRorx] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    simp only [Option.some.injEq] at h; subst h; rfl
  | andn d a b => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | bswap d => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | shift op d n =>
    simp only [exec, execShift] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | movImm64 d v => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | vpmovmskb len d r => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | movdquLoad d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | movdquStore m r => exact store128_widen hw h
  | xop op => simp only [exec, Option.some.injEq] at h ⊢; subst h; cases op <;> rfl
  | vop op =>
    simp only [exec, Option.some.injEq] at h ⊢; subst h
    cases op <;> simp only [VOp.exec] <;> (try split) <;> rfl
  | vmovdquLoad len d m =>
    cases len
    · simp only [exec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [exec]
      rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
    · simp only [exec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [exec]
      rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv]; rfl
  | vbroadcasti128 d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | vmovdquStore len m r =>
    cases len
    · exact store128_widen hw h
    · exact store256_widen hw h
  | zop op =>
    simp only [exec, Option.some.injEq] at h ⊢; subst h; cases op <;> rfl
  | vmovdqu32Load d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load512_widen hc hv]; rfl
  | vbroadcasti32x4 d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | zbcst op d a m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load64_widen hc hv]; rfl
  | vmovdqu32Store m r => exact store512_widen hw h
  | stmxcsr m => exact store32_widen hw h
  | ldmxcsr m =>
    simp only [exec, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    simp only [exec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load32_widen hc hv, Option.bind_some]
    split at h <;> [cases h; cases h]
    rename_i hr; simp only [hr, ite_true]; rfl
  | lfence => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | mul r => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | mulx hi lo src =>
    simp only [exec, execMulx] at h ⊢
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, rfl⟩
  | adcx d src =>
    simp only [exec, execAdcx] at h ⊢
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, c, hc', rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, c, hc', rfl⟩
  | adox d src =>
    simp only [exec, execAdox] at h ⊢
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, c, hc', rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, c, hc', rfl⟩
  | push | pop => simp only [exec, reduceCtorEq] at h

theorem addrs_withRegions (i : Instr) (s : State) (rd wr : List Region) :
    addrs i (s.withRegions rd wr) = addrs i s := by
  cases i <;> rfl

theorem exec_regions {i : Instr} (h : exec i s = some s') : s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | store m r =>
    simp only [exec, State.store64] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | store32 m r =>
    simp only [exec, State.store32] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | store8 m r =>
    simp only [exec, State.store8] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | movdquStore m r =>
    simp only [exec, State.store128] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | movdquLoad d m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | xop op => simp only [exec, Option.some.injEq] at h; subst h; cases op <;> exact ⟨rfl, rfl⟩
  | vop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]; exact ⟨rfl, rfl⟩
  | vmovdquLoad len d m =>
    cases len <;> simp only [exec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
      exact ⟨rfl, rfl⟩
  | vbroadcasti128 d m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | vmovdquStore len m r =>
    cases len
    · simp only [exec, State.store128] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
    · simp only [exec, State.store256] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | zop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]; exact ⟨rfl, rfl⟩
  | vmovdqu32Load d m | vbroadcasti32x4 d m | zbcst _ d _ m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | vmovdqu32Store m r =>
    simp only [exec, State.store512] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | stmxcsr m =>
    simp only [exec, State.store32] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | ldmxcsr m =>
    simp only [exec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
    split at h <;> cases h; exact ⟨rfl, rfl⟩
  | lfence => simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | mul r => simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | mulx hi lo src =>
    simp only [exec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | push | pop => simp only [exec, reduceCtorEq] at h
  | _ => exact ⟨(Taint.exec_nonstore rfl h).1, (Taint.exec_nonstore rfl h).2.1⟩

theorem exec_frame {i : Instr} (h : exec i s = some s') : Frame s.wr s.mem s'.mem := by
  cases i with
  | store m r =>
    simp only [exec, State.store64] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | store32 m r =>
    simp only [exec, State.store32] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | store8 m r =>
    simp only [exec, State.store8] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | movdquStore m r =>
    simp only [exec, State.store128] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | movdquLoad d m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | xop op =>
    simp only [exec, Option.some.injEq] at h; subst h; cases op <;> exact Frame.refl _ _
  | vop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]; exact Frame.refl _ _
  | vmovdquLoad len d m =>
    cases len <;> simp only [exec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
      exact Frame.refl _ _
  | vbroadcasti128 d m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | vmovdquStore len m r =>
    cases len
    · simp only [exec, State.store128] at h; split at h <;> cases h
      rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
    · simp only [exec, State.store256] at h; split at h <;> cases h
      rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | zop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]; exact Frame.refl _ _
  | vmovdqu32Load d m | vbroadcasti32x4 d m | zbcst _ d _ m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | vmovdqu32Store m r =>
    simp only [exec, State.store512] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | stmxcsr m =>
    simp only [exec, State.store32] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | ldmxcsr m =>
    simp only [exec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
    split at h <;> cases h; exact Frame.refl _ _
  | lfence => simp only [exec, Option.some.injEq] at h; subst h; exact Frame.refl _ _
  | mul r => simp only [exec, Option.some.injEq] at h; subst h; exact Frame.refl _ _
  | mulx hi lo src =>
    simp only [exec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | push | pop => simp only [exec, reduceCtorEq] at h
  | _ => rw [(Taint.exec_nonstore rfl h).2.2.1]; exact Frame.refl _ _

theorem eval_withRegions (c : Cond) (s : State) (rd wr : List Region) :
    eval c (s.withRegions rd wr) = eval c s := by
  cases c <;> rfl

end

theorem execBlock_regions {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw⟩ := exec_regions he
    obtain ⟨hr', hw', hf⟩ := ih h2
    exact ⟨hr'.trans hr, hw'.trans hw, (exec_frame he).trans (hw ▸ hf)⟩

theorem call_regions {s s' : State} (h : isa.call s = some s') : s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem ret_regions {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.rd = s₂.rd ∧ s'.wr = s₂.wr := by
  simp only [isa, ret] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- Calls and returns change only `rsp` (by 8 each way), and the memory. -/
theorem call_gpr {s s' : State} (h : isa.call s = some s') (r : Reg) :
    s'.gpr r = if r = .rsp then s.gpr .rsp - 8 else s.gpr r := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_gpr {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') (r : Reg) :
    s₂.gpr .rsp = s₁.gpr .rsp ∧ s'.gpr r = if r = .rsp then s₂.gpr .rsp + 8 else s₂.gpr r := by
  simp only [isa, ret] at h; split at h <;> cases h; rename_i hc; exact ⟨hc.1, rfl⟩

theorem ofNat_eight_mul_succ (n : Nat) :
    BitVec.ofNat 64 (8 * (n + 1)) = BitVec.ofNat 64 (8 * n) + 8 := by
  rw [show 8 * (n + 1) = 8 * n + 8 by omega, BitVec.ofNat_add]; rfl

theorem pushRegs_eq (s : State) (rs : List Reg) :
    (pushRegs s rs).rd = s.rd ∧ (pushRegs s rs).wr = s.wr ∧
      (pushRegs s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length) ∧
      ∀ r, r ≠ .rsp → (pushRegs s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, by simp [pushRegs], fun _ _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih { s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) }
    refine ⟨h₁, h₂, ?_, fun r hr => ?_⟩
    · simp only [pushRegs, h₃, List.length_cons, ofNat_eight_mul_succ]
      simp only [State.setReg, ite_true]
      rw [BitVec.sub_sub, BitVec.add_comm]
    · simp only [pushRegs, h₄ r hr]
      simp [State.setReg, hr]

theorem popReg_eq (s : State) (d : Reg) (k : Nat) :
    (popReg s d k).rd = s.rd ∧ (popReg s d k).wr = s.wr ∧
      (popReg s d k).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (8 * k) ∧
      ∀ r, r ≠ .rsp → r ≠ d → (popReg s d k).gpr r = s.gpr r := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl, by simp [popReg], fun _ _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih ((s.setReg d (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp
      (s.gpr .rsp + 8))
    refine ⟨h₁, h₂, ?_, fun r hr hr' => ?_⟩
    · simp only [popReg, h₃, ofNat_eight_mul_succ]
      simp only [State.setReg, ite_true]
      rw [BitVec.add_assoc, BitVec.add_comm (8 : BitVec 64)]
    · simp only [popReg, h₄ r hr hr']
      simp [State.setReg, hr, hr']

theorem pushRegs_withRegions (s : State) (rs : List Reg) (rd wr : List Region) :
    pushRegs (s.withRegions rd wr) rs = (pushRegs s rs).withRegions rd wr := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    exact ih { s.setReg .rsp (s.gpr .rsp - 8) with mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) }

theorem popReg_withRegions (s : State) (d : Reg) (k : Nat) (rd wr : List Region) :
    popReg (s.withRegions rd wr) d k = (popReg s d k).withRegions rd wr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    exact ih ((s.setReg d (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8))

/-- A frame's push adds its region at the head of `wr`, and changes no
register but `rsp`. -/
theorem push_eq {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ k, s₁.rd = s.rd ∧ s₁.wr = ⟨s₁.gpr .rsp, 8 * k⟩ :: s.wr ∧
      (∀ r, r ≠ .rsp → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * k) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h
  rename_i rs _
  obtain ⟨h₁, -, h₃, h₄⟩ := pushRegs_eq s rs
  exact ⟨rs.length, h₁, by rw [h₃], h₄, h₃⟩

/-- A frame's pop removes the region at the head of `wr`, and changes only
its register and `rsp`. -/
theorem pop_eq {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s₂.wr = s₁.wr ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr.tail ∧
      (∀ r, r ≠ .rsp → Taint.clobbers j r = false → s'.gpr r = s₂.gpr r) ∧
      s₂.gpr .rsp = s₁.gpr .rsp ∧
      ∃ k, s₁.wr.head? = some ⟨s₁.gpr .rsp, 8 * k⟩ ∧
        s'.gpr .rsp = s₂.gpr .rsp + BitVec.ofNat 64 (8 * k) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  rename_i d k hc
  obtain ⟨h₁, -, h₃, h₄⟩ := popReg_eq s₂ d k
  refine ⟨hc.2.2.2.1, h₁, rfl, fun r hr hd => h₄ r hr ?_, hc.2.2.1, k, hc.2.2.2.2, h₃⟩
  intro e; subst e; simp [Taint.clobbers] at hd

theorem push_widen {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) (rd wr : List Region) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧
      isa.push i (s.withRegions rd wr) = some (s₁.withRegions rd (f :: wr)) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h
  rename_i rs hc
  refine ⟨_, (pushRegs_eq s rs).1, rfl, ?_⟩
  simp only [isa, push, State.withRegions_gpr, ne_eq, hc.1, hc.2.1, hc.2.2, not_false_eq_true,
    and_self, ite_true, pushRegs_withRegions]
  rfl

theorem pop_widen {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') (rd : List Region)
    {wr : List Region} (hw : wr.head? = s₁.wr.head?) :
    isa.pop j (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s'.withRegions rd wr.tail) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h
  rename_i hc
  simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, ne_eq, hw, hc.1, hc.2.1,
    hc.2.2.1, hc.2.2.2.2, and_self, ite_true, not_false_eq_true, popReg_withRegions]
  rfl

/-- The permissions never change. -/
theorem Exec.rdwr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction h with
  | block h => exact ⟨(execBlock_regions h).1, (execBlock_regions h).2.1⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂.1.trans ih₁.1, ih₂.2.trans ih₁.2⟩
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ⟨ih₂.1.trans ih₁.1, ih₂.2.trans ih₁.2⟩
  | frame hp _ hq ih =>
    obtain ⟨k, r₁, w₁, -⟩ := push_eq hp
    obtain ⟨-, r₂, w₂, -⟩ := pop_eq hq
    exact ⟨r₂.trans (ih.1.trans r₁), by rw [w₂, ih.2, w₁]; rfl⟩
  | call hc _ hr ih =>
    obtain ⟨r₁, w₁⟩ := call_regions hc; obtain ⟨r₂, w₂⟩ := ret_regions hr
    exact ⟨r₂.trans (ih.1.trans r₁), w₂.trans (ih.2.trans w₁)⟩

/-- Code that calls no function changes memory only within the regions it
may write (a call also stores its return address below the stack pointer). -/
theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noCalls = true) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem := by
  induction h with
  | block h => exact execBlock_regions h
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    obtain ⟨r₁, w₁, f₁⟩ := ih₁ hn.1; obtain ⟨r₂, w₂, f₂⟩ := ih₂ hn.2
    exact ⟨r₂.trans r₁, w₂.trans w₁, f₁.trans (w₁ ▸ f₂)⟩
  | iteT _ _ ih => simp only [Code.noCalls, Bool.and_eq_true] at hn; exact ih hn.1
  | iteF _ _ ih => simp only [Code.noCalls, Bool.and_eq_true] at hn; exact ih hn.2
  | loopExit _ _ ih => exact ih hn
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, f₁⟩ := ih₁ hn; obtain ⟨r₂, w₂, f₂⟩ := ih₂ hn
    exact ⟨r₂.trans r₁, w₂.trans w₁, f₁.trans (w₁ ▸ f₂)⟩
  | frame => simp [Code.noCalls] at hn
  | call => simp [Code.noCalls] at hn

theorem execBlock_widen {is : List Instr} {s s' : State} {t : List Leak} {rd wr : List Region}
    (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr)
    (h : execBlock isa is s = some (s', t)) :
    execBlock isa is (s.withRegions rd wr) = some (s'.withRegions rd wr, t) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw'⟩ := exec_regions he
    have := ih (s := s₁) (by rwa [hr, hw']) (by rwa [hw']) h2
    simp only [execBlock]
    rw [show exec i (s.withRegions rd wr) = some (s₁.withRegions rd wr) from exec_widen hc hw he]
    simp only [this, Option.map_some, addrs_withRegions]

/-- Running from a state that permits more memory. -/
theorem Exec.widen {c : Prog isa} {s s' : State} {t : List Leak} {rd wr : List Region}
    (h : Exec isa c s t s') (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    Exec isa c (s.withRegions rd wr) t (s'.withRegions rd wr) := by
  induction h generalizing rd wr with
  | block h => exact .block (execBlock_widen hc hw h)
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁⟩ := Exec.rdwr h₁
    exact .seq (ih₁ hc hw) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | iteT hc' _ ih => exact .iteT ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | iteF hc' _ ih => exact .iteF ((eval_withRegions _ _ _ _).trans ‹_›) (ih hc hw)
  | loopExit h₁ hc' ih => exact .loopExit (ih hc hw) ((eval_withRegions _ _ _ _).trans ‹_›)
  | loopNext h₁ hc' _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁⟩ := Exec.rdwr h₁
    exact .loopNext (ih₁ hc hw) ((eval_withRegions _ _ _ _).trans ‹_›) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | @frame i j _ s₀ _ s₂ _ _ hp _ hq ih =>
    obtain ⟨f, r₁, w₁, hp'⟩ := push_widen hp rd wr
    have hq' := pop_widen hq rd (wr := f :: wr) (by rw [w₁]; rfl)
    have hb := ih (rd := rd) (wr := f :: wr) (by rw [r₁, w₁]; exact Covers.push f hc)
      (by rw [w₁]; exact Covers.push (xs := []) (xs' := []) f hw)
    have := Exec.frame hp' hb hq'
    have e₁ : isa.addrs i (s₀.withRegions rd wr) = isa.addrs i s₀ := addrs_withRegions _ _ _ _
    have e₂ : isa.addrs j (s₂.withRegions rd (f :: wr)) = isa.addrs j s₂ :=
      addrs_withRegions _ _ _ _
    rw [e₁, e₂] at this
    exact this
  | @call n _ s₀ s₁ s₂ s₃ _ hc₁ _ hr ih =>
    obtain ⟨r₁, w₁⟩ := call_regions hc₁
    have hc' : isa.call (s₀.withRegions rd wr) = some (s₁.withRegions rd wr) := by
      simp only [isa, call, Option.some.injEq] at hc₁ ⊢; subst hc₁; rfl
    have hr' : isa.ret (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s₃.withRegions rd wr) := by
      simp only [isa, ret] at hr ⊢
      split at hr <;> cases hr
      rename_i h
      exact (ite_eq_left h).trans rfl
    have := Exec.call (name := n) hc' (ih (by rwa [r₁, w₁]) (by rwa [w₁])) hr'
    exact this

theorem exec_gpr {i : Instr} {r : Reg} (hi : Taint.clobbers i r = false) {s s' : State}
    (h : exec i s = some s') : s'.gpr r = s.gpr r := by
  cases hd : Taint.dstOf i with
  | some d =>
    refine (Taint.exec_nonstore hd h).2.2.2 r fun h' => ?_
    subst h'
    cases i <;> simp_all [Taint.clobbers, Taint.dstOf]
  | none =>
    cases i <;> simp only [Taint.dstOf, reduceCtorEq] at hd
    · simp only [exec, State.store64] at h; split at h <;> cases h; rfl
    · simp only [exec, State.store32] at h; split at h <;> cases h; rfl
    · simp only [exec, State.store8] at h; split at h <;> cases h; rfl
    · simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [exec, State.store128] at h; split at h <;> cases h; rfl
    · simp only [exec, Option.some.injEq] at h; subst h; rename_i op; cases op <;> rfl
    · simp only [exec, Option.some.injEq] at h; subst h; rename_i op
      rw [Taint.VOp.exec_eq op s]
    · rename_i len _ _; cases len <;> simp only [exec, Option.map_eq_some_iff] at h <;>
        obtain ⟨_, _, rfl⟩ := h <;> rfl
    · rename_i len _ _; cases len
      · simp only [exec, State.store128] at h; split at h <;> cases h; rfl
      · simp only [exec, State.store256] at h; split at h <;> cases h; rfl
    · simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [exec, Option.some.injEq] at h; subst h; rename_i op
      rw [Taint.ZOp.exec_eq op s]
    · simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [exec, State.store512] at h; split at h <;> cases h; rfl
    · simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [exec, State.store32] at h; split at h <;> cases h; rfl
    · simp only [exec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
      split at h <;> cases h; rfl
    · simp only [exec, Option.some.injEq] at h; subst h; rfl
    · rename_i q
      simp only [Taint.clobbers, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
      simp only [exec, Option.some.injEq] at h; subst h
      exact Taint.execMul_gpr q s hi.1 hi.2
    · rename_i hi' lo src
      simp only [Taint.clobbers, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
      simp only [exec, execMulx] at h; split at h
      · cases h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
        exact Taint.mulx_gpr s _ _ hi.1 hi.2
    · simp only [exec, reduceCtorEq] at h
    · simp only [exec, reduceCtorEq] at h

theorem execBlock_gpr {is : List Instr} {r : Reg} (hc : ∀ i ∈ is, Taint.clobbers i r = false)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.gpr r = s.gpr r := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2,
      exec_gpr (hc i (List.mem_cons_self ..)) he]

/-- A register that no instruction writes keeps its value. -/
theorem Exec.gpr {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.gpr r = s.gpr r := by
  induction h with
  | block h => exact execBlock_gpr hc h
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ fun i hi => hc i (List.mem_append_right _ hi), ih₁ fun i hi => hc i (List.mem_append_left _ hi)]
  | iteT _ _ ih => exact ih fun i hi => hc i (List.mem_append_left _ hi)
  | iteF _ _ ih => exact ih fun i hi => hc i (List.mem_append_right _ hi)
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | frame hp _ hq ih =>
    obtain ⟨k, -, w₁, g₁, e₁⟩ := push_eq hp
    obtain ⟨-, -, -, g₂, e₂, k', h₃, e₃⟩ := pop_eq hq
    have hb := ih (fun i hi => hc i (by simp [instrs, hi]))
    by_cases hrs : r = .rsp
    · subst hrs
      rw [w₁] at h₃
      simp only [List.head?_cons, Option.some.injEq, Region.mk.injEq] at h₃
      have : k = k' := by omega
      subst this
      rw [e₃, hb, e₁, BitVec.sub_add_cancel]
    · rw [g₂ r hrs (hc _ (by simp [instrs])), hb, g₁ r hrs]
  | call hc₁ _ hr ih =>
    obtain ⟨hsp, h'⟩ := ret_gpr hr r
    rw [h']
    by_cases hrs : r = .rsp
    · subst hrs
      rw [ite_eq_left rfl, hsp, call_gpr hc₁, ite_eq_left rfl]
      exact BitVec.sub_add_cancel _ _
    · simp only [hrs, ite_false, ih hc, call_gpr hc₁]

/-- A register that no instruction writes keeps its value, as a
postcondition. -/
theorem WP.gpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {r : Reg}
    (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false) : WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

/-- Inlining verified code: from a state `s` in which the code's precondition
holds once its permissions are narrowed to `rd` and `wr`, the code
terminates in a state satisfying its postcondition and calling-convention
obligations (both on the narrowed states), which has the permissions of `s`,
differs from it in memory only within `wr`, and keeps every register that no
instruction writes. -/
theorem WP.inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa c s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl habi hf (fun r hr => Exec.gpr hr he') ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hpost

/-- Widening writable regions: code verified against `k` is verified against
a contract `k'` whose states permit writing regions that extend (same bases,
at least as long) the ones `k` permits (`wr s`), reading the same ones, if
`k'` asks nothing more. The code runs as it does from the narrowed state,
with the same trace and result. -/
theorem Verified.widen {c : Prog isa} {k k' : Contract isa} (h : Verified target c k)
    (wr : State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (s.withRegions s.rd (wr s)))
    (hwr : ∀ s, k'.pre s → List.Forall₂ Region.Prefix (wr s) s.wr)
    (hpost : ∀ s s', k'.pre s →
      k.post (s.withRegions s.rd (wr s)) (s'.withRegions s.rd (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (s₁.withRegions s₁.rd (wr s₁)) (s₂.withRegions s₂.rd (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified target c k' := by
  refine h.of_narrow (fun s => s.withRegions s.rd (wr s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    hpre (fun s t s₁ hs he => ?_) (fun s t s₁ hs he ha hq => ?_) hpub hsat
  · have hw : Covers (wr s) s.wr := fun _ _ => InRegions.of_prefix (hwr s hs)
    have := Exec.widen (rd := s.rd) (wr := s.wr) he (Covers.append (fun _ _ h => h) hw) hw
    rwa [State.withRegions_withRegions, State.withRegions_self] at this
  · obtain ⟨hr, hw⟩ := Exec.rdwr he
    simp only [State.withRegions_rd, State.withRegions_wr] at hr hw
    have : (s₁.withRegions s.rd s.wr).withRegions s.rd (wr s) = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hw]; rfl
    exact ⟨ha, hpost s _ hs (by rw [this]; exact hq)⟩

end VG.X86_64
