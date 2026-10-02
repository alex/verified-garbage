import VerifiedGarbage.Proof.AesGcm.X86.CryptTail

/-!
# AES-GCM on x86: what every function does

Untrusted: everything here is checked by Lean. Each function takes `W`
from its stack arguments, saves our caller's `ebx, esi, edi, ebp` at
`W + 128` (`save_ok`), copies arguments to their slots in `W` (`keeps_ok`)
and in the end restores the registers (`exit_ok`); the pieces it runs in
between never write `W + 128` to `W + 240` (`keptR`).

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- The address of the stack argument `i` on entry, with `esp = SP`. -/
abbrev argA (SP : BitVec 32) (i : Nat) : Addr := w64 (SP + BitVec.ofNat 32 (4 + 4 * i))

/-- The `n` stack arguments on entry. -/
abbrev argsR (SP : BitVec 32) (n : Nat) : Region := ⟨w64 (SP + BitVec.ofNat 32 4), 4 * n⟩

theorem argA_eq {SP : BitVec 32} {n i : Nat} (hi : i < n) (hf : SP.toNat + 4 + 4 * n ≤ 2 ^ 32) :
    argA SP i = w64 (SP + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * i) := by
  rw [argA, ← add_ofNat_assoc32]
  exact w64_add (by rw [toNat_add32 (by omega)]; omega)

theorem argA_sub {SP : BitVec 32} {n i : Nat} (hi : i < n) (hf : SP.toNat + 4 + 4 * n ≤ 2 ^ 32) :
    Region.Sub ⟨argA SP i, 4⟩ (argsR SP n) := by
  rw [argA_eq hi hf]; exact Offset.sub_base _ (by omega)

theorem argA_contains {SP : BitVec 32} {n i : Nat} (hi : i < n) (hf : SP.toNat + 4 + 4 * n ≤ 2 ^ 32) :
    (argsR SP n).Contains (argA SP i) 4 := by
  rw [argA_eq hi hf]; exact Offset.contains_base _ (by omega) (by omega)

/-- Where `saveAt` puts our caller's registers. -/
def SavedAt (m : Mem) (W : BitVec 32) (s₀ : State) : Prop :=
  slotv m W 128 = s₀.gpr .ebx ∧ slotv m W 132 = s₀.gpr .esi ∧ slotv m W 136 = s₀.gpr .edi ∧
    slotv m W 140 = s₀.gpr .ebp

/-- The saved registers' slots. -/
abbrev savedR (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 128, 16⟩

theorem SavedAt.frame {m m' : Mem} {W : BitVec 32} {s₀ : State} (h : SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savedR W).Disjoint r) : SavedAt m' W s₀ := by
  have k : ∀ {o}, 128 ≤ o → o + 4 ≤ 144 → slotv m' W o = slotv m W o := fun h₁ h₂ =>
    slot_frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))
  exact ⟨by rw [k (by decide) (by decide)]; exact h.1, by rw [k (by decide) (by decide)]; exact h.2.1,
    by rw [k (by decide) (by decide)]; exact h.2.2.1, by rw [k (by decide) (by decide)]; exact h.2.2.2⟩

theorem SavedAt.frameK {m m' : Mem} {W : BitVec 32} {s₀ : State} (h : SavedAt m W s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (keptR W).Disjoint r) : SavedAt m' W s₀ :=
  h.frame hf fun r hr => (hd r hr).sub_left (Offset.sub _ (by decide) (by decide))

/-- The registers saved, and `ebp := W`. -/
theorem save_ok (s : State) {W : BitVec 32} (ha : s.gpr .eax = W) (hw : Covers [⟨w64 W, 2560⟩] s.wr)
    (fw : W.toNat + 2560 ≤ 2 ^ 32) :
    ∃ s', runBlock isa saveAt s = some s' ∧ s'.gpr .ebp = W ∧ (∀ r, r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ SavedAt s'.mem W s ∧
      Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s'.mem := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have wIn : ∀ {o}, o + 4 ≤ 2560 → InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hw ho (by decide)
  refine ⟨_, by xrun [saveAt, ha, aW, wIn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · regs [ha]
  · intro r hr; simp only [gpr_setMem, gpr_setReg_of_ne _ _ hr]
  · rfl
  · rfl
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [slotv_eq]; mems [])
  · have c : ∀ d, 128 ≤ d → d + 4 ≤ 144 →
        (⟨w64 W + BitVec.ofNat 64 128, 16⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) 4 :=
      fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
    simp only [mem_setMem, gpr_setMem, mem_setReg]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 128 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 132 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 136 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 140 (by decide) (by decide))

/-- What the copies of stack arguments into `W` need. -/
structure KeepEnv (W SP : BitVec 32) (n : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  wW : Covers [⟨w64 W, 2560⟩] s.wr
  rA : Covers [argsR SP n] (s.rd ++ s.wr)
  aw : (argsR SP n).Disjoint ⟨w64 W, 2560⟩
  fa : SP.toNat + 4 + 4 * n ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32

theorem KeepEnv.keep {W SP : BitVec 32} {n : Nat} {s s' : State} (h : KeepEnv W SP n s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    KeepEnv W SP n s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], by rw [hwr]; exact h.wW, by rw [hrd, hwr]; exact h.rA, h.aw, h.fa, h.fw⟩

theorem KeepEnv.argIn {W SP : BitVec 32} {n : Nat} {s : State} (h : KeepEnv W SP n s) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (argA SP i) 4 :=
  h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains hi h.fa⟩

theorem KeepEnv.argW {W SP : BitVec 32} {n : Nat} {s : State} (h : KeepEnv W SP n s) {i : Nat} (hi : i < n)
    {o : Nat} (ho : o + 4 ≤ 2560) : (⟨argA SP i, 4⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 o, 4⟩ :=
  (h.aw.sub_left (argA_sub hi h.fa)).sub_right (Lay.wSub ho)

/-- `keep i o`. -/
theorem keep_ok {W SP : BitVec 32} {n : Nat} {s : State} (h : KeepEnv W SP n s) {i o : Nat} (hi : i < n)
    (ho : o + 4 ≤ 2560) :
    ∃ s', runBlock isa (keep i o) s = some s' ∧
      s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 o) (s.mem.readW (argA SP i) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o := w64_add (by have := h.fw; omega)
  have wIn : InRegions s.wr (w64 W + BitVec.ofNat 64 o) 4 := in_off h.wW ho (by decide)
  have rIn := h.argIn hi
  refine ⟨_, by xrun [keep, h.esp, h.ebp, aW, wIn, rIn], ?_, ?_, ?_, ?_⟩
  · mems []
  · intro r hr; simp only [gpr_setMem, gpr_setReg_of_ne _ _ hr]
  all_goals rfl

/-- The slot of `p`'s copy. -/
abbrev keepR (W : BitVec 32) (p : Nat × Nat) : Region := ⟨w64 W + BitVec.ofNat 64 p.2, 4⟩

/-- The copies of the arguments `ps` (argument, offset): each slot holds its argument. -/
theorem keeps_ok {W SP : BitVec 32} {n : Nat} (ps : List (Nat × Nat))
    (hps : ∀ p ∈ ps, p.1 < n ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0) (hnd : (ps.map (·.2)).Nodup)
    {s : State} (h : KeepEnv W SP n s) :
    ∃ s', runBlock isa (ps.flatMap fun p => keep p.1 p.2) s = some s' ∧
      (∀ p ∈ ps, slotv s'.mem W p.2 = s.mem.readW (argA SP p.1) 32) ∧
      Frame (ps.map (keepR W)) s.mem s'.mem ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ps generalizing s with
  | nil => exact ⟨s, rfl, fun _ h => by simp at h, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨hp1, hp2, hp4⟩ := hps p (List.mem_cons_self ..)
    obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := keep_ok h hp1 hp2
    have h₁ : KeepEnv W SP n s₁ := h.keep (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨s', run', sl, fr, g', rd', wr'⟩ :=
      ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hnd'.2 h₁
    have fw : Frame [keepR W p] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have argS : ∀ q ∈ ps, s₁.mem.readW (argA SP q.1) 32 = s.mem.readW (argA SP q.1) 32 := fun q hq => by
      have := hps q (List.mem_cons_of_mem _ hq)
      exact fw.readW (r := ⟨argA SP q.1, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.argW this.1 hp2) (by decide)
    refine ⟨s', runBlock_app_of run₁ run', fun q hq => ?_, ?_, fun r hr => by rw [g' r hr, g₁ r hr],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [slotv_eq, fr.readW (r := keepR W q) (Region.contains_self _ _) (fun r hr => ?_) (by decide), m₁,
          Mem.readW_writeW_self32]
        simp only [List.mem_map] at hr
        obtain ⟨q', hq', rfl⟩ := hr
        have ne : q'.2 ≠ q.2 := fun e => hnd'.1 (List.mem_map.mpr ⟨q', hq', e⟩)
        have := hps q' (List.mem_cons_of_mem _ hq')
        exact Lay.w_w (by omega) (by omega) (by omega)
      · rw [sl q hq, argS q hq]
    · exact (fw.mono (by simp)).trans (fr.mono (fun r hr => List.mem_cons_of_mem _ hr))

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : BitVec 32} (hbp : s.gpr .ebp = W) (hsp : s.gpr .esp = s₀.gpr .esp)
    (hr : Covers [⟨w64 W, 2560⟩] (s.rd ++ s.wr)) (fw : W.toNat + 2560 ≤ 2 ^ 32) (hs : SavedAt s.mem W s₀)
    (hret : s.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have aW : ∀ {o}, o < 2560 → w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
    fun ho => w64_add (by omega)
  have rIn : ∀ {o}, o + 4 ≤ 2560 → InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 o) 4 :=
    fun ho => in_off hr ho (by decide)
  obtain ⟨e₁, e₂, e₃, e₄⟩ := hs
  simp only [slotv_eq] at e₁ e₂ e₃ e₄
  refine WP.of_runBlock ⟨_, by xrun [restore, hbp, aW, rIn], ⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · regs [e₁]
    · regs [e₂]
    · regs [e₃]
    · regs [e₄]
    · regs [hsp]
  · simp only [mem_setReg]; exact hret
  · mems []
  · regs []
  · mems []
  · mems []

/-- After the entry's copies: what the rest of the entry block starts from. -/
structure Entered (s : State) (W St : BitVec 32) (nA : Nat) (ps : List (Nat × Nat)) (s₂ : State) : Prop where
  ebp : s₂.gpr .ebp = W
  esi : s₂.gpr .esi = St
  esp : s₂.gpr .esp = s.gpr .esp
  ebx : s₂.gpr .ebx = s.gpr .ebx
  edi : s₂.gpr .edi = s.gpr .edi
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  saved : SavedAt s₂.mem W s
  slots : ∀ p ∈ ps, slotv s₂.mem W p.2 = arg s p.1
  args : ∀ i < nA, s₂.mem.readW (argA (s.gpr .esp) i) 32 = arg s i
  frame : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₂.mem

/-- The entry: `W` from the stack argument `w`, the registers saved, the
state pointer into `esi` (by `pre`), the arguments `ps` copied, then `tail`. -/
theorem entry_gen {s : State} {w nA : Nat} (pre : List Instr) (ps : List (Nat × Nat)) (tail : List Instr)
    {W St : BitVec 32} (hw : w < nA)
    (hps : ∀ p ∈ ps, p.1 < nA ∧ 144 ≤ p.2 ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0) (hnd : (ps.map (·.2)).Nodup)
    (hW : arg s w = W) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [argsR (s.gpr .esp) nA] (s.rd ++ s.wr)) (aw : (argsR (s.gpr .esp) nA).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32)
    (hpre : ∀ s₁ : State, s₁.gpr .ebp = W → s₁.gpr .esp = s.gpr .esp → s₁.rd = s.rd → s₁.wr = s.wr →
      (∀ i < nA, s₁.mem.readW (argA (s.gpr .esp) i) 32 = arg s i) →
      ∃ s₂, runBlock isa pre s₁ = some s₂ ∧ s₂.gpr .esi = St ∧ (∀ r, r ≠ .esi → s₂.gpr r = s₁.gpr r) ∧
        s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr)
    {Q : State → Prop} (ht : ∀ s₂, Entered s W St nA ps s₂ → ∃ s₃, runBlock isa tail s₂ = some s₃ ∧ Q s₃) :
    WP isa (entry w (pre ++ (ps.flatMap (fun p => keep p.1 p.2) ++ tail))) s Q := by
  generalize hSP : s.gpr .esp = SP at rA aw fa hpre
  have argIn : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ {i}, i < nA → InRegions (t.rd ++ t.wr) (argA SP i) 4 :=
    fun hrd hwr _ hi => by rw [hrd, hwr]; exact rA _ _ ⟨_, List.mem_singleton_self _, argA_contains hi fa⟩
  have i₀ := argIn rfl rfl hw
  have aW : (argsR SP nA).Disjoint ⟨w64 W, 2560⟩ := aw
  refine WP.seq (WP.of_runBlock ⟨_, by xrun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP w) 32)).gpr .eax = W := by
    rw [gpr_setReg_self, ← hSP]; exact hW
  set s₀ := s.setReg .eax (s.mem.readW (argA SP w) 32) with hs₀
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have f₁' : Frame [⟨w64 W + BitVec.ofNat 64 128, 16⟩] s.mem s₁.mem := f₁
  have hA₁ : ∀ i < nA, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁'.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aW.sub_left (argA_sub hi fa)).sub_right (Lay.wSub (by decide))) (by decide)]
    rw [arg, argAddr, hSP]
  obtain ⟨s₂, run₂, si₂, g₂, m₂, rd₂, wr₂⟩ := hpre s₁ bp₁ sp₁ rd₁ wr₁ hA₁
  have ke : KeepEnv W SP nA s₂ := ⟨by rw [g₂ _ (by decide), bp₁], by rw [g₂ _ (by decide), sp₁],
    by rw [wr₂, wr₁]; exact wW, by rw [rd₂, wr₂, rd₁, wr₁]; exact rA, aW, fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok ps (fun p hp => ⟨(hps p hp).1, (hps p hp).2.2⟩) hnd ke
  -- The arguments are apart from `W`, so the stores keep them.
  have argW : ∀ {i}, i < nA → ∀ r ∈ [(⟨w64 W + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨argA SP i, 4⟩ : Region).Disjoint r := fun hi r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (aW.sub_left (argA_sub hi fa)).sub_right (Lay.wSub (by decide))
  have f₃' : Frame [⟨w64 W + BitVec.ofNat 64 128, 2432⟩] s.mem s₃.mem := by
    refine (f₁'.sub fun r hr => ?_).trans ((m₂ ▸ f₃).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      have := hps p hp
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  have hargs : ∀ i < nA, s₃.mem.readW (argA SP i) 32 = arg s i := fun i hi =>
    (f₃'.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi) (by decide)).trans (by
      rw [arg, argAddr, hSP])
  have hsv : SavedAt s₃.mem W s := by
    have := sv₁.frame (m₂ ▸ f₃) fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      have := hps p hp
      exact Lay.w_w (.inl (by omega)) (by decide) (by omega)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  obtain ⟨s₄, run₄, q⟩ := ht s₃ ⟨by rw [g₃ _ (by decide), g₂ _ (by decide), bp₁],
    by rw [g₃ _ (by decide), si₂],
    by rw [g₃ _ (by decide), g₂ _ (by decide), sp₁, hSP],
    by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide)],
    by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide)],
    by rw [rd₃, rd₂, rd₁]; rfl, by rw [wr₃, wr₂, wr₁]; rfl, hsv,
    fun p hp => by rw [sl₃ p hp, m₂]; exact hA₁ p.1 (hps p hp).1, by rw [hSP]; exact hargs, f₃'⟩
  exact WP.of_runBlock ⟨s₄, runBlock_app_of run₁ (runBlock_app_of run₂ (runBlock_app_of run₃ run₄)), q⟩

/-- The entry with the state pointer the stack argument `k`. -/
theorem entry_ok {s : State} {w k nA : Nat} (ps : List (Nat × Nat)) (tail : List Instr) {W St : BitVec 32}
    (hw : w < nA) (hk : k < nA)
    (hps : ∀ p ∈ ps, p.1 < nA ∧ 144 ≤ p.2 ∧ p.2 + 4 ≤ 2560 ∧ p.2 % 4 = 0) (hnd : (ps.map (·.2)).Nodup)
    (hW : arg s w = W) (hSt : arg s k = St) (wW : Covers [⟨w64 W, 2560⟩] s.wr)
    (rA : Covers [argsR (s.gpr .esp) nA] (s.rd ++ s.wr)) (aw : (argsR (s.gpr .esp) nA).Disjoint ⟨w64 W, 2560⟩)
    (fa : (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32) (fw : W.toNat + 2560 ≤ 2 ^ 32) {Q : State → Prop}
    (ht : ∀ s₂, Entered s W St nA ps s₂ → ∃ s₃, runBlock isa tail s₂ = some s₃ ∧ Q s₃) :
    WP isa (entry w ([.mov .esi (argOp k)] ++ (ps.flatMap (fun p => keep p.1 p.2) ++ tail))) s Q := by
  refine entry_gen _ ps tail hw hps hnd hW wW rA aw fa fw (fun s₁ bp sp rd wr ha => ?_) ht
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (argA (s.gpr .esp) k) 4 := by
    rw [rd, wr]; exact rA _ _ ⟨_, List.mem_singleton_self _, argA_contains hk fa⟩
  have v := ha k hk
  refine ⟨_, by xrun [sp, i₁, v], ?_, ?_, ?_, ?_, ?_⟩
  · regs [hSt]
  · intro r hr; simp only [gpr_setReg_of_ne _ _ hr]
  all_goals rfl

end VG.Proof.AesGcm.X86
