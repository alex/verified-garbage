import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Iterate
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on ARMv7: constant time

As on AArch64 (`Proof/Pbkdf2/AArch64/IterateCT.lean`): this holds for any
compression function (`CompOk`), so it is proven once. The taint analysis
cannot prove it without looking into the compression function (it would lose
our registers, which the compression function saves and restores in a scratch
space it also stores secrets into through a register that is not the base of a
region), so we relate two runs (`RelCT`): at every point, correctness
determines our registers from the public arguments alone, so they agree;
between the calls, the taint analysis proves each block constant time from
that (`Checks`, evaluated for each hash function, since the code depends on
its sizes); and the calls are constant time by the compression function's own
proof (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Iterate

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash xorW)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.Arm (wp_mov op2_reg eval_eq eval_ne)
open VG.Proof.Pbkdf2.Stream.Arm (iterG)
open VG.Spec.Sha256 (bytesAt)

/-- The registers the blocks between the calls use. -/
abbrev regsS : List Reg := [.r0, .r3, .r4, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `iterate` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block H.prologue) hc).isSome = true
  load : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (H.loadKey 0)) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (H.digest ++ H.loadKey (H.N + H.B))) hc).isSome = true
  fin : ∃ hc, (taint.check (Taint.ofRegs regsS) (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++
    [.subs .r5 .r5 (.imm 1)])) hc).isSome = true
  epi : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block H.st.restore) hc).isSome = true
  ite : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

theorem PubEq.nn {s₀ s₀' : State} (hq : PubEq s₀ s₀') : nn s₀ = nn s₀' := congrArg BitVec.toNat hq.r2

/-- The state during a step, with `v` in `r5`. -/
structure St (H : Hash) (sc : Nat) (md : Md H.B H.N H.L) (s₀ : State) (v : BitVec 32) (s : State) : Prop
    extends Regs H sc s₀ s where
  r5 : s.gpr .r5 = v
  pad : bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D

section
variable {H : Hash} {sc : Nat} {md : Md H.B H.N H.L}

/-- The registers the blocks use agree in two runs. -/
theorem St.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {v : BitVec 32} {s s' : State} (h : St H sc md s₀ v s)
    (h' : St H sc md s₀' v s') : ∀ r ∈ regsS, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r0, h'.r0, hv, hv, scr, scr, hq.a0]
  · rw [h.r3, h'.r3, scr, scr, hq.a0]
  · rw [h.r4, h'.r4, key, key, hq.r0]
  · rw [h.r5, h'.r5]
  · rw [h.r6, h'.r6, blk, blk, scr, scr, hq.a0]
  · rw [h.r7, h'.r7, tp, tp, hq.r3]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

theorem St.of_inv {s₀ : State} {r : Nat} {s : State} (h : Inv H sc md s₀ (r + 1) s) :
    St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s :=
  ⟨h.toRegs, h.r5, h.pad⟩

variable (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀) {v : BitVec 32}
include hz hp

/-! ## What each piece of a step does, in one run -/

theorem load_st (hR : md.Reloc) {o : Nat} (ho : o + H.N ≤ 2 * (H.N + H.B)) (ho4 : o % 4 = 0) {s : State}
    (h : St H sc md s₀ v s) :
    WP isa (.block (H.loadKey o)) s (St H sc md s₀ v) := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.pad; have := hz.NL
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [← List.append_nil (H.loadKey o)]
  exact load_ok hz hp hR h.toRegs ho ho4 fun s' g rd wr sp f _ => WP.block_nil
    ⟨h.toRegs.write (fun r hr => g r (ne12 r hr)) rd wr sp (frame_scr (a := H.hvO) (by simp only [Hash.hvO]; omega) f),
      (g _ (by decide)).trans h.r5,
      (Memory.frame_bytesAt f (fun r hr => blk_disj hz hp (by omega) r (by simp at hr; simp [hr])) (by omega)).trans
        h.pad⟩

theorem cmp_st (hf : CompOk md H.so H.compC) {s : State} (h : St H sc md s₀ v s) :
    WP isa H.compressBlock s (St H sc md s₀ v) := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.pad; have := hz.NL
  have : H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  exact cmp_ok hz hp hf h.toRegs fun s' h' x5 f _ =>
    ⟨h', x5.trans h.r5, (Memory.frame_bytesAt f (blk_disj hz hp (by omega)) (by omega)).trans h.pad⟩

theorem mid_st (ho : OutOk md H.out) (hR : md.Reloc) {s : State} (h : St H sc md s₀ v s) :
    WP isa (.block (H.digest ++ H.loadKey (H.N + H.B))) s (St H sc md s₀ v) := by
  have := hz.N64; have := hp.fits; have := hz.NL; have := hz.N4
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  refine digest_ok hz hp ho h.toRegs h.pad fun s' g rd wr sp f _ p => ?_
  exact load_st hz hp hR (by omega) (by omega)
    ⟨h.toRegs.write (fun r hr => g r (ne9 r hr) (ne10 r hr) (ne12 r hr)) rd wr sp
      (frame_scr (a := H.blkO) (by simp only [Hash.blkO]; omega) f),
      (g _ (by decide) (by decide) (by decide)).trans h.r5, p⟩

/-! ## Two runs -/

variable {s₀' : State} (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')
include hp' hq

theorem cmp_rel (hf : CompOk md H.so H.compC) :
    RelCT isa (fun s s' => St H sc md s₀ v s ∧ St H sc md s₀' v s') H.compressBlock fun s s' =>
      St H sc md s₀ v s ∧ St H sc md s₀' v s' := by
  have e : hv H s₀' = hv H s₀ ∧ scr s₀' = scr s₀ ∧ blk H s₀' = blk H s₀ := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hv, blk, scr, hq.a0]
  have call := compressBlock_rel (H := md) (so := H.so) hf (name := H.compN) (st := hv H s₀) (scr := scr s₀)
    (src := blk H s₀) (P' := fun s s' => St H sc md s₀ v s ∧ St H sc md s₀' v s')
    fun s s' ⟨h, h'⟩ => by
      have c' := callOk_of hz hp' h'.toRegs
      rw [e.1, e.2.1, e.2.2] at c'
      exact ⟨callOk_of hz hp h.toRegs, c'⟩
  exact (call.wp fun _ _ h => ⟨cmp_st hz hp hf h.1, cmp_st hz hp' hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

omit hz in
/-- A block the taint analysis checks from `regsS`. -/
theorem blk_rel {c : Prog isa} {G : State → State → Prop}
    (hc : ∃ hc, (taint.check (Taint.ofRegs regsS) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre H sc t₀ → ∀ s, St H sc md t₀ v s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => St H sc md s₀ v s ∧ St H sc md s₀' v s') c fun s s' => G s₀ s ∧ G s₀' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h =>
    Taint.agree_ofRegs (St.agree hq h.1 h.2)) hc).wp fun _ _ h => ⟨hw hp _ h.1, hw hp' _ h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel (ho : OutOk md H.out) (hR : md.Reloc) (hf : CompOk md H.so H.compC) (hc : Checks H) {r : Nat} :
    RelCT isa (fun s s' => Inv H sc md s₀ (r + 1) s ∧ Inv H sc md s₀' (r + 1) s') H.body
      fun s s' => (eval .ne s = some (r != 0) ∧ Inv H sc md s₀ r s) ∧
        (eval .ne s' = some (r != 0) ∧ Inv H sc md s₀' r s') := by
  have := hz.N64; have := hz.NL
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have l0 : RelCT isa (fun s s' => St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧
      St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s') (.block (H.loadKey 0))
      fun s s' => St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧ St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s' :=
    blk_rel hp hp' hq (G := fun t₀ => St H sc md t₀ (BitVec.ofNat 32 (r + 1))) hc.load
      fun hp _ h => load_st hz hp hR (by omega) rfl h
  have dl : RelCT isa (fun s s' => St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧
      St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s') (.block (H.digest ++ H.loadKey (H.N + H.B)))
      fun s s' => St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧ St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s' :=
    blk_rel hp hp' hq (G := fun t₀ => St H sc md t₀ (BitVec.ofNat 32 (r + 1))) hc.mid
      fun hp _ h => mid_st hz hp ho hR h
  obtain ⟨_, hfi⟩ := hc.fin
  have fin : RelCT isa (fun s s' => St H sc md s₀ (BitVec.ofNat 32 (r + 1)) s ∧
      St H sc md s₀' (BitVec.ofNat 32 (r + 1)) s')
      (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++ [.subs .r5 .r5 (.imm 1)])) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs regsS) (fun _ _ h => Taint.agree_ofRegs (St.agree hq h.1 h.2)) hfi
  have c := cmp_rel hz hp hp' hq (v := BitVec.ofNat 32 (r + 1)) hf
  have hb : RelCT isa (fun s s' => Inv H sc md s₀ (r + 1) s ∧ Inv H sc md s₀' (r + 1) s') H.body fun _ _ => True :=
    fun s s' t t' u u' h e e' => by
      unfold Hash.body at e e'
      exact (l0.seq (c.seq (dl.seq (c.seq fin)))) s s' t t' u u' ⟨St.of_inv h.1, St.of_inv h.2⟩ e e'
  exact (hb.wp fun _ _ h => ⟨body_ok hz hp ho hR hf h.1, body_ok hz hp' ho hR hf h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop_rel (ho : OutOk md H.out) (hR : md.Reloc) (hf : CompOk md H.so H.compC) (hc : Checks H) {n : Nat} :
    RelCT isa (fun s s' => Inv H sc md s₀ (n + 1) s ∧ Inv H sc md s₀' (n + 1) s') (.loop H.body .ne)
      fun _ _ => True :=
  RelCT.loop (M := isa) (body := H.body) (c := .ne) (Q := fun _ _ => True)
    (fun m s s' => Inv H sc md s₀ (m + 1) s ∧ Inv H sc md s₀' (m + 1) s') (fun m => by
      intro s s' t t' u u' h e e'
      obtain ⟨ht, ⟨z, i⟩, ⟨z', i'⟩⟩ := body_rel hz hp hp' hq ho hR hf hc _ _ _ _ _ _ h e e'
      refine ⟨ht, z.trans z'.symm, fun _ => trivial, fun hc' => ?_⟩
      have hc'' : some (m != 0) = some true := z.symm.trans hc'
      cases m with
      | zero => cases hc''
      | succ m => exact ⟨m, by omega, i, i'⟩) n

end

theorem iterate_rel {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀)
    (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.iterate fun _ _ => True := by
  have hz := hH.sizes
  obtain ⟨_, hpr⟩ := hc.pro
  obtain ⟨_, hep⟩ := hc.epi
  obtain ⟨_, hit⟩ := hc.ite
  have hlt : ∀ {s₀ : State}, nn s₀ < 2 ^ 32 := fun {s₀} => (s₀.gpr .r2).isLt
  have aw : ∀ {t : State}, Pre H sc t →
      t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := fun {t} h => by
    have e : (⟨State.addr t.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.a_t
    · exact h.a_s
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.prologue) fun s s' =>
      (Inv H sc hH.md s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0)) ∧
        (Inv H sc hH.md s₀' (nn s₀') s' ∧ s'.z = decide (nn s₀' = 0)) :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) ⟨_, hpr⟩
      (fun _ e => by rw [e]; exact prologue_ok hz hp hH.len)
      (fun _ e => by rw [e]; exact prologue_ok hz hp' hH.len)
  have br : RelCT isa (fun s s' => (Inv H sc hH.md s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0)) ∧
        (Inv H sc hH.md s₀' (nn s₀') s' ∧ s'.z = decide (nn s₀' = 0)))
      (.ite .eq (.block []) (.loop H.body .ne))
      fun s s' => Inv H sc hH.md s₀ 0 s ∧ Inv H sc hH.md s₀' 0 s' := by
    refine (RelCT.ite (fun s s' h => ?_) (RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by simp)) hit) ?_).wp
      (fun _ _ h => ⟨loop_ok hz hp hH.out hH.reloc hH.comp h.1.1 h.1.2,
        loop_ok hz hp' hH.out hH.reloc hH.comp h.2.1 h.2.2⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2
    · show eval .eq s = eval .eq s'
      rw [eval_eq, eval_eq, h.1.2, h.2.2, hq.nn]
    · intro s s' t t' u u' ⟨⟨⟨i, zi⟩, ⟨i', _⟩⟩, hc'⟩ e e'
      have hc'' : some (decide (nn s₀ = 0)) = some false := by rw [← zi, ← eval_eq]; exact hc'
      have hne : nn s₀ ≠ 0 := fun h0 => by rw [h0] at hc''; cases hc''
      obtain ⟨m, hm⟩ : ∃ m, nn s₀ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hne).symm⟩
      rw [hm] at i
      rw [← hq.nn, hm] at i'
      exact loop_rel hz hp hp' hq hH.out hH.reloc hH.comp hc _ _ _ _ _ _ ⟨i, i'⟩ e e'
  have epi : RelCT isa (fun s s' => Inv H sc hH.md s₀ 0 s ∧ Inv H sc hH.md s₀' 0 s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r11]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.1.r11, h.2.r11, scr, scr, hq.a0]) hep
  unfold Hash.iterate
  exact pro.seq (br.seq epi)

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (iterG S W).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `iterate` is verified against `iterG`, for any hash function the proof
supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} (hfit : H.st.buf + H.N + H.B ≤ 8 * sc)
    (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified Arm.target H.iterate (iterG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (iterate_rel hH hc (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.Iterate
