import VerifiedGarbage.Proof.Rc4.X86.ApplyStep
import VerifiedGarbage.Proof.Rc4.Update

/-! # RC4 on x86 (32-bit): the stream loop -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem sep_of_sub {R₁ R₂ : Region} (h : R₁.Disjoint R₂) {a b : Addr} {n k : Nat}
    (h₁ : R₁.Contains a n) (h₂ : R₂.Contains b k) : Mem.Sep a n b k :=
  fun x hx hy => h x (h₁.byte hx) (h₂.byte hy)

theorem contains_prefix (p : Addr) {n k : Nat} (h : n ≤ k) : (⟨p, k⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
  exact h

/-- `vg_rc4_apply(ctx, data, len, scratch)`: what its proof needs on entry. -/
structure ApplyPre (s : State) (P D L Sc : BitVec 32) : Prop where
  aP : arg s 0 = P
  aD : arg s 1 = D
  aL : arg s 2 = L
  aS : arg s 3 = Sc
  args : InRegions s.rd (argAddr s 0) 16
  ctx : InRegions s.wr (P.setWidth 64) 258
  data : InRegions s.wr (D.setWidth 64) L.toNat
  scratch : InRegions s.wr (Sc.setWidth 64) 64
  ctxFit : P.toNat + 258 ≤ 2 ^ 32
  dataFit : D.toNat + L.toNat ≤ 2 ^ 32
  scratchFit : Sc.toNat + 64 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  ctxData : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨D.setWidth 64, L.toNat⟩
  ctxScratch : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨Sc.setWidth 64, 64⟩
  dataScratch : Region.Disjoint ⟨D.setWidth 64, L.toNat⟩ ⟨Sc.setWidth 64, 64⟩
  argsCtx : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨P.setWidth 64, 258⟩
  argsData : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨D.setWidth 64, L.toNat⟩
  argsScratch : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨Sc.setWidth 64, 64⟩

/-- What the function writes: the context, the data and `scratch`. -/
def applyRegions (P D L Sc : BitVec 32) : List Region :=
  [⟨P.setWidth 64, 258⟩, ⟨D.setWidth 64, L.toNat⟩, ⟨Sc.setWidth 64, 64⟩]

/-- What the stream loop writes: the table, `scratch[16]` and the data. -/
def loopRegions (P D L Sc : BitVec 32) : List Region :=
  [⟨P.setWidth 64, 256⟩, ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩, ⟨D.setWidth 64, L.toNat⟩]

theorem loop_sub_apply (P D L Sc : BitVec 32) :
    ∀ r ∈ loopRegions P D L Sc, ∃ r' ∈ applyRegions P D L Sc, Region.Sub r r' := by
  intro r hr
  simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩

theorem arg_contains' {s : State} (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  have h : argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    unfold argAddr
    rw [VG.Proof.MlKem.X86.ea_off (by omega), VG.Proof.MlKem.X86.ea_off (by omega),
      BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [h]
  exact Offset.contains_base _ (by omega) (by omega)

namespace ApplyPre

variable {s : State} {P D L Sc : BitVec 32}

theorem arg_in (hp : ApplyPre s P D L Sc) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  obtain ⟨r, hr, hc⟩ := hp.args
  have hc' := arg_contains' hp.spFit hi
  refine ⟨r, List.mem_append_left _ hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [← Offset.sub_add_sub_cancel (argAddr s i) (argAddr s 0) r.base, BitVec.toNat_add]
  omega

theorem arg_disjoint (hp : ApplyPre s P D L Sc) :
    ∀ r ∈ applyRegions P D L Sc, Region.Disjoint ⟨argAddr s 0, 16⟩ r := by
  intro r hr
  simp only [applyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.argsCtx
  · exact hp.argsData
  · exact hp.argsScratch

theorem arg_eq (hp : ApplyPre s P D L Sc) {m : Mem} (hf : Frame (applyRegions P D L Sc) s.mem m)
    {i : Nat} (hi : i < 4) : m.readW (argAddr s i) 32 = arg s i :=
  hf.readW (arg_contains' hp.spFit hi) hp.arg_disjoint (by decide)

/-- What a stream iteration needs, from what the function's memory keeps. -/
theorem env {t : State} (hp : ApplyPre s P D L Sc) (hf : Frame (applyRegions P D L Sc) s.mem t.mem)
    (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hdi : t.gpr .edi = P) : StepEnv t P D L Sc := by
  have ac (i : Nat) (hi : i < 4) := arg_contains' hp.spFit (s := s) hi
  have hT : (⟨P.setWidth 64, 258⟩ : Region).Contains (P.setWidth 64) 256 :=
    contains_prefix _ (by decide)
  have hS : (⟨Sc.setWidth 64, 64⟩ : Region).Contains (Sc.setWidth 64 + BitVec.ofNat 64 16) 4 :=
    Offset.contains_base _ (by decide) (by decide)
  have hD : (⟨D.setWidth 64, L.toNat⟩ : Region).Contains (D.setWidth 64) L.toNat :=
    contains_prefix _ (Nat.le_refl _)
  refine
    { p := hdi
      pfit := by have := hp.ctxFit; omega
      sfit := hp.scratchFit
      dfit := hp.dataFit
      table := ?_
      spill := by rw [hwr]; exact region_offset _ _ _ 16 4 (by decide) (by decide) hp.scratch
      data := by rw [hwr]; exact hp.data
      a8 := by rw [hrd, hwr, hsp]; exact hp.arg_in (i := 1) (by decide)
      a12 := by rw [hrd, hwr, hsp]; exact hp.arg_in (i := 2) (by decide)
      a16 := by rw [hrd, hwr, hsp]; exact hp.arg_in (i := 3) (by decide)
      v8 := by rw [hsp]; exact (hp.arg_eq hf (i := 1) (by decide)).trans hp.aD
      v12 := by rw [hsp]; exact (hp.arg_eq hf (i := 2) (by decide)).trans hp.aL
      v16 := by rw [hsp]; exact (hp.arg_eq hf (i := 3) (by decide)).trans hp.aS
      s8T := by rw [hsp]; exact sep_of_sub hp.argsCtx (ac 1 (by decide)) hT
      s12T := by rw [hsp]; exact sep_of_sub hp.argsCtx (ac 2 (by decide)) hT
      s16T := by rw [hsp]; exact sep_of_sub hp.argsCtx (ac 3 (by decide)) hT
      s8S := by rw [hsp]; exact sep_of_sub hp.argsScratch (ac 1 (by decide)) hS
      s12S := by rw [hsp]; exact sep_of_sub hp.argsScratch (ac 2 (by decide)) hS
      s16S := by rw [hsp]; exact sep_of_sub hp.argsScratch (ac 3 (by decide)) hS
      s8D := by rw [hsp]; exact sep_of_sub hp.argsData (ac 1 (by decide)) hD
      s12D := by rw [hsp]; exact sep_of_sub hp.argsData (ac 2 (by decide)) hD
      s16D := by rw [hsp]; exact sep_of_sub hp.argsData (ac 3 (by decide)) hD
      sTS := sep_of_sub hp.ctxScratch hT hS
      sTD := sep_of_sub hp.ctxData hT hD
      sSD := sep_of_sub hp.dataScratch.symm hS hD }
  rw [hwr]
  have h := region_offset _ _ _ 0 256 (by decide) (by decide) hp.ctx
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

end ApplyPre

/-- The context and output after the first `k` data bytes. -/
def upd (s : State) (P D : BitVec 32) (k : Nat) : Context × List Byte :=
  update (contextAt s.mem (P.setWidth 64)) (bytesAt s.mem (D.setWidth 64) k)

theorem upd_succ (s : State) (P D : BitVec 32) (k : Nat) :
    upd s P D (k + 1) = ((step (upd s P D k).1).1, (upd s P D k).2 ++
      [s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ (step (upd s P D k).1).2]) := by
  unfold upd
  rw [bytes_snoc, update_snoc]

/-- The stream loop after `k` bytes, `m₁` being the memory it started from. -/
structure LoopInv (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (P.setWidth 64)).table = (upd s P D k).1.table
  i : t.gpr .esi = (upd s P D k).1.i.setWidth 32
  j : t.gpr .ebp = (upd s P D k).1.j.setWidth 32
  data : bytesAt t.mem (D.setWidth 64) k = (upd s P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (D.setWidth 64 + BitVec.ofNat 64 x) = s.mem (D.setWidth 64 + BitVec.ofNat 64 x)
  frame : Frame (loopRegions P D L Sc) m₁ t.mem
  bx : t.gpr .ebx = BitVec.ofNat 32 k
  p : t.gpr .edi = P
  sp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- A byte outside the table, `scratch[16]` and the data byte an iteration writes. -/
theorem step_other {m : Mem} {p q d x : Addr} {ii jj : Byte} {v : BitVec 32} {w : Byte}
    (hT : ¬ (x - p).toNat < 256) (hS : ¬ (x - q).toNat < 4) (hD : x ≠ d) :
    ((((m.write (p + BitVec.ofNat 64 jj.toNat) 1 (m (p + BitVec.ofNat 64 ii.toNat))).write
      (p + BitVec.ofNat 64 ii.toNat) 1 (m (p + BitVec.ofNat 64 jj.toNat))).writeW q v).write d 1 w) x =
      m x := by
  rw [write_byte, ite_eq_right hD]
  unfold Mem.writeW
  rw [Mem.write_apply hS]
  exact swap_frame m p ii jj x hT

theorem data_ne {D : BitVec 32} {L : BitVec 32} {x k : Nat}
    (hx : x < L.toNat) (hk : k < L.toNat) (hne : x ≠ k) :
    D.setWidth 64 + BitVec.ofNat 64 x ≠ D.setWidth 64 + BitVec.ofNat 64 k := by
  intro h
  have h' := congrArg (fun y => (y - D.setWidth 64).toNat) h
  simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  exact hne h'

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (t : State) (i j : Byte) (P D L Sc : BitVec 32) (k : Nat)
    (hsi : t.gpr .esi = i.setWidth 32) (hbp : t.gpr .ebp = j.setWidth 32)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 k) (hk : k < L.toNat) (he : StepEnv t P D L Sc) :
    let next := step { table := (contextAt t.mem (P.setWidth 64)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (P.setWidth 64)).table = next.1.table ∧
      u.gpr .esi = next.1.i.setWidth 32 ∧ u.gpr .ebp = next.1.j.setWidth 32 ∧
      u.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
        t.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - P.setWidth 64).toNat < 256 →
        ¬ (x - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 4 →
        x ≠ D.setWidth 64 + BitVec.ofNat 64 k → u.mem x = t.mem x) ∧
      Frame (loopRegions P D L Sc) t.mem u.mem ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.gpr .edi = P ∧ u.gpr .esp = t.gpr .esp ∧
      u.gpr .ebx = BitVec.ofNat 32 (k + 1) ∧
      u.zf = some (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step t i j P D L Sc k hsi hbp hbx hk he)
    fun u ⟨hum, hurd, huwr, hudi, husp, husi, hubp, hubx, huz⟩ => ?_
  have hdk : ¬ (D.setWidth 64 + BitVec.ofNat 64 k - P.setWidth 64).toNat < 256 ∧
      ¬ (D.setWidth 64 + BitVec.ofNat 64 k - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 4 := by
    have hin : (D.setWidth 64 + BitVec.ofNat 64 k - D.setWidth 64).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk
    exact ⟨fun h => he.sTD _ h hin, fun h => he.sSD _ h hin⟩
  have hTD : Mem.Sep (P.setWidth 64) 256 (D.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    sep_offset_right he.sTD (by omega) (by omega)
  refine ⟨?_, husi, hubp, ?_, ?_, ?_, hurd, huwr, hudi, husp, hubx, huz⟩
  · rw [hum]
    unfold Mem.writeW
    rw [table_write_sep' _ _ _ _ hTD, table_write_sep' _ _ _ _ he.sTS, table_swap]
  · rw [hum, write_byte, ite_eq_left rfl]
    unfold Mem.writeW
    rw [Mem.write_apply hdk.2]
    rw [swap_frame _ _ _ _ _ hdk.1]
    have ht := table_swap t.mem (P.setWidth 64) (i + 1#8)
      (j + t.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]
  · intro x hT hS hD
    rw [hum]
    exact step_other hT hS hD
  · rw [hum]
    have hP : (⟨P.setWidth 64, 256⟩ : Region) ∈ loopRegions P D L Sc := List.mem_cons_self
    have hS : (⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩ : Region) ∈ loopRegions P D L Sc :=
      List.mem_cons_of_mem _ List.mem_cons_self
    have hD : (⟨D.setWidth 64, L.toNat⟩ : Region) ∈ loopRegions P D L Sc :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    refine Frame.write ?_ hD _ (Offset.contains_base _ (by omega) (by omega))
    refine Frame.writeW ?_ hS _ (contains_prefix _ (by decide))
    refine Frame.write ?_ hP _ (Offset.contains_base _ (by omega) (by omega))
    exact Frame.write (Frame.refl _ _) hP _ (Offset.contains_base _ (by omega) (by omega))

theorem loop_step (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (hp : ApplyPre s P D L Sc)
    (hb : Frame (applyRegions P D L Sc) s.mem m₁) {k : Nat} (hk : k < L.toNat) (t : State)
    (ht : LoopInv s P D L Sc m₁ k t) :
    WP isa (.block applyStep) t fun u => LoopInv s P D L Sc m₁ (k + 1) u ∧
      u.zf = some (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  have hft : Frame (applyRegions P D L Sc) s.mem t.mem :=
    hb.trans (ht.frame.sub (loop_sub_apply P D L Sc))
  have he := hp.env hft ht.sp ht.rd ht.wr ht.p
  have hsD : ∀ x, x < L.toNat →
      ¬ (D.setWidth 64 + BitVec.ofNat 64 x - P.setWidth 64).toNat < 256 ∧
      ¬ (D.setWidth 64 + BitVec.ofNat 64 x - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 4 := by
    intro x hx
    have hin : (D.setWidth 64 + BitVec.ofNat 64 x - D.setWidth 64).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hx
    exact ⟨fun h => he.sTD _ h hin, fun h => he.sSD _ h hin⟩
  have hctx : (⟨(contextAt t.mem (P.setWidth 64)).table, (upd s P D k).1.i, (upd s P D k).1.j⟩ :
      Context) = (upd s P D k).1 := context_ext ht.table rfl rfl
  have hst := apply_step_table t (upd s P D k).1.i (upd s P D k).1.j P D L Sc k ht.i ht.j ht.bx hk he
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hurd, huwr, hudi, husp, hubx, huz⟩ =>
    ⟨?_, huz⟩
  have hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (D.setWidth 64 + BitVec.ofNat 64 x) = t.mem (D.setWidth 64 + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx).1 (hsD x hx).2 (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [upd_succ]; exact htab
      i := by rw [upd_succ]; exact hui
      j := by rw [upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega)]
        exact ht.tail x (by omega) hxL
      frame := ht.frame.trans hfr
      bx := hubx
      p := hudi
      sp := husp.trans ht.sp
      rd := hurd.trans ht.rd
      wr := huwr.trans ht.wr }
  rw [bytes_snoc, upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
  refine congrArg (· ++ _) ?_
  exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega) (by omega)

theorem apply_loop (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (hp : ApplyPre s P D L Sc)
    (hb : Frame (applyRegions P D L Sc) s.mem m₁) {k : Nat} (hk : k < L.toNat) (t : State)
    (ht : LoopInv s P D L Sc m₁ k t) :
    WP isa (.loop (.block applyStep) .ne) t (LoopInv s P D L Sc m₁ L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ LoopInv s P D L Sc m₁ j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (loop_step s P D L Sc m₁ hp hb hj u hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    simp only [eval, hz, Option.map_some]
    rfl
  · right
    have hL := L.isLt
    have hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    refine ⟨?_, L.toNat - (j + 1), by omega, j + 1, by omega, rfl, hv⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

end VG.Proof.Rc4.X86
