import VerifiedGarbage.Proof.Scrypt.X86_64.Rounds
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Scrypt.X86_64.Contract

/-!
# The Salsa20/8 Core on x86-64: loading, finishing, saving and restoring

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Scrypt.X86_64

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .rdi
/-- `scratch`. -/
abbrev sp : Addr := s₀.gpr .rsi
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bufAt (bp s₀) (4 * j.1)) 32
end

abbrev bR (p : Addr) : Region := ⟨p, 64⟩

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR (bp s₀), scR (sp s₀)]
  b_sc : (bR (bp s₀)).Disjoint (scR (sp s₀))
  ret_b : (retR s₀).Disjoint (bR (bp s₀))
  ret_sc : (retR s₀).Disjoint (scR (sp s₀))

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem Pre.hb {s₀ : State} (hp : Pre s₀) : bR (bp s₀) ∈ s₀.wr := by simp [hp.wr]
theorem Pre.hs {s₀ : State} (hp : Pre s₀) : scR (sp s₀) ∈ s₀.wr := by simp [hp.wr]

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bufAt (bp s₀) (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem in_b {rs ws : List Region} {p : Addr} (hw : bR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (bufAt p d) n :=
  ⟨bR p, List.mem_append_right _ hw, contains_off h (by omega)⟩

theorem out_b {ws : List Region} {p : Addr} (hw : bR p ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (bufAt p d) n :=
  ⟨bR p, hw, contains_off h (by omega)⟩

/-- A part of a region: `[p + d, p + d + n)` inside `[p, p + len)`. -/
theorem sub_off (p : Addr) {len d n : Nat} (h : d + n ≤ len) (hl : len < 2 ^ 32) :
    Region.Sub ⟨bufAt p d, n⟩ ⟨p, len⟩ := by
  intro x hx
  simp only [Region.Contains, bufAt, ofInt_natCast] at *
  have : (x - p).toNat ≤ (x - (p + BitVec.ofNat 64 d)).toNat + d := by
    rw [show x - p = (x - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-- Reading `b` after writes to `scratch` only. -/
theorem read_b {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [scR (sp s₀)] s₀.mem m)
    {k : Nat} (hk : k < 16) : m.readW (bufAt (bp s₀) (4 * k)) 32 = (V s₀)[k] := by
  rw [V_get _ hk]
  refine hf.readW (r := ⟨bufAt (bp s₀) (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.b_sc.sub_left (sub_off _ (by omega) (by omega))

/-- Reading `scratch` after writes to `b` only. -/
theorem read_sc {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [bR (bp s₀)] m m')
    {d w : Nat} (hd : d + w / 8 ≤ 64) (hw : w / 8 < 2 ^ 64) :
    m'.readW (bufAt (sp s₀) d) w = m.readW (bufAt (sp s₀) d) w := by
  refine hf.readW (r := ⟨bufAt (sp s₀) d, w / 8⟩) (Region.contains_self _ _) ?_ hw
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.b_sc.symm.sub_left (sub_off _ hd (by omega))

theorem mem_read {s : State} {r : Reg} {d : Nat}
    (hin : InRegions (s.rd ++ s.wr) (bufAt (s.gpr r) d) 4) :
    readSrc32 s (.mem (at_ r d)) = some (s.mem.readW (bufAt (s.gpr r) d) 32) := by
  simp only [readSrc32, ea_at, State.load32, hin, ite_true]

/-! ## Saving the callee-saved registers -/

/-- The memory after the prologue's stores. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (bufAt (sp s₀) 16) (s₀.gpr .rbx)).writeW (bufAt (sp s₀) 24)
    (s₀.gpr .rbp)).writeW (bufAt (sp s₀) 32) (s₀.gpr .r12)).writeW (bufAt (sp s₀) 40)
    (s₀.gpr .r13)).writeW (bufAt (sp s₀) 48) (s₀.gpr .r14)).writeW (bufAt (sp s₀) 56)
    (s₀.gpr .r15)

/-- The callee-saved registers are saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (bufAt (sp s₀) 16) 64 = s₀.gpr .rbx ∧ m.readW (bufAt (sp s₀) 24) 64 = s₀.gpr .rbp ∧
  m.readW (bufAt (sp s₀) 32) 64 = s₀.gpr .r12 ∧ m.readW (bufAt (sp s₀) 40) 64 = s₀.gpr .r13 ∧
  m.readW (bufAt (sp s₀) 48) 64 = s₀.gpr .r14 ∧ m.readW (bufAt (sp s₀) 56) 64 = s₀.gpr .r15

theorem save_eq : save = [
    .store (at_ .rsi 16) .rbx, .store (at_ .rsi 24) .rbp, .store (at_ .rsi 32) .r12,
    .store (at_ .rsi 40) .r13, .store (at_ .rsi 48) .r14, .store (at_ .rsi 56) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .rsi 16)), .mov .rbp (.mem (at_ .rsi 24)), .mov .r12 (.mem (at_ .rsi 32)),
    .mov .r13 (.mem (at_ .rsi 40)), .mov .r14 (.mem (at_ .rsi 48)), .mov .r15 (.mem (at_ .rsi 56))] :=
  rfl

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := out_sc hp.hs (d := 16) (n := 8) (by omega)
  have o1 := out_sc hp.hs (d := 24) (n := 8) (by omega)
  have o2 := out_sc hp.hs (d := 32) (n := 8) (by omega)
  have o3 := out_sc hp.hs (d := 40) (n := 8) (by omega)
  have o4 := out_sc hp.hs (d := 48) (n := 8) (by omega)
  have o5 := out_sc hp.hs (d := 56) (n := 8) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, isa, ea_at, State.store64, o0, o1, o2,
    o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

theorem readW64_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (bufAt p e) v).readW (bufAt p d) 64 = m.readW (bufAt p d) 64 :=
  Mem.readW_writeW_sep (off_sep p hd he (by omega) (by omega) h) (by decide)

set_option simprocs false in
theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_writeW_off]

theorem saveMem_frame (s₀ : State) : Frame [scR (sp s₀)] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 64 → (scR (sp s₀)).Contains (bufAt (sp s₀) d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 16 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 24 (by omega))).writeW (List.mem_singleton_self _) _
    (c 32 (by omega))).writeW (List.mem_singleton_self _) _ (c 40 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 48 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 56 (by omega))

/-- The saved registers survive writes to the slots and to `b`. -/
theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m₁ m' : Mem} (h : Saved s₀ m)
    (hf₁ : Frame [slotR (sp s₀)] m m₁) (hf₂ : Frame [bR (bp s₀)] m₁ m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 16 ≤ d → d + 8 ≤ 64 →
      m'.readW (bufAt (sp s₀) d) 64 = m.readW (bufAt (sp s₀) d) 64 := by
    intro d h1 h2
    rw [read_sc hp hf₂ (by omega) (by decide)]
    refine hf₁.readW (r := ⟨bufAt (sp s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr x hx hy
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, bufAt, ofInt_natCast] at hx hy
    bv_omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 16 (by omega) (by omega)).trans h1, (key 24 (by omega) (by omega)).trans h2,
    (key 32 (by omega) (by omega)).trans h3, (key 40 (by omega) (by omega)).trans h4,
    (key 48 (by omega) (by omega)).trans h5, (key 56 (by omega) (by omega)).trans h6⟩

set_option simprocs false in
theorem restore_ok {s₀ : State} {s : State} (hs : Saved s₀ s.mem) (hrsi : s.gpr .rsi = sp s₀)
    (hw : scR (sp s₀) ∈ s.wr) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rsp = s.gpr .rsp ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r := by
  have i0 := in_sc (rs := s.rd) hw (d := 16) (n := 8) (by omega)
  have i1 := in_sc (rs := s.rd) hw (d := 24) (n := 8) (by omega)
  have i2 := in_sc (rs := s.rd) hw (d := 32) (n := 8) (by omega)
  have i3 := in_sc (rs := s.rd) hw (d := 40) (n := 8) (by omega)
  have i4 := in_sc (rs := s.rd) hw (d := 48) (n := 8) (by omega)
  have i5 := in_sc (rs := s.rd) hw (d := 56) (n := 8) (by omega)
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hs
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hrsi, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true})

/-! ## Loading the words -/

/-- The load invariant after `n` words, relative to the state `s₁` after the
prologue's stores. -/
structure LI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ k (hk : k < 12), k < n → s.gpr (wreg k) = ((V s₀)[k]'(by omega)).setWidth 64
  slots : ∀ k (hk : k < 16), 12 ≤ k → k < n → s.mem.readW (bufAt (sp s₀) (slotOff k)) 32 = (V s₀)[k]
  frame : Frame [slotR (sp s₀)] s₁.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = sp s₀
  rdi : s.gpr .rdi = bp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem sub_slot_sc (p : Addr) : ∀ r ∈ [slotR p], ∃ r' ∈ [scR p], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scR p, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩

theorem load_step {s₀ s₁ : State} (hp : Pre s₀) (hf₁ : Frame [scR (sp s₀)] s₀.mem s₁.mem)
    {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ s₁ n s) :
    WP isa (.block (loadWord n)) s (LI s₀ s₁ (n + 1)) := by
  have hfs : Frame [scR (sp s₀)] s₀.mem s.mem := hf₁.trans (h.frame.sub (sub_slot_sc _))
  have hr : readSrc32 s (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
    rw [mem_read (by rw [h.rdi, h.rd, h.wr]; exact in_b hp.hb (by omega)), h.rdi, read_b hp hfs hn]
  unfold loadWord
  split
  · rename_i hn12
    refine wp_cons (mov32_upd (d := wreg n) hr) fun s' u => WP.block_nil ?_
    have ne := wreg_ne n hn12
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, u.mem ▸ h.frame, u.rd.trans h.rd,
      u.wr.trans h.wr, (u.other _ ne.2.1.symm).trans h.rsi, (u.other _ ne.2.2.1.symm).trans h.rdi,
      (u.other _ ne.2.2.2.symm).trans h.rsp⟩
    · by_cases e : k = n
      · subst e; exact u.gpr
      · rw [u.other _ fun h' => e (wreg_inj k hk n hn12 h'), h.regs k hk (by omega)]
    · rw [u.mem]; exact h.slots k hk h12 (by omega)
  · rename_i hn12
    refine wp_cons (mov32_upd (d := .rax) hr) fun s' u => ?_
    have hout : InRegions s'.wr (s'.ea (at_ .rsi (slotOff n))) 4 := by
      rw [ea_at, u.other _ (by decide), h.rsi, u.wr, h.wr]
      exact out_sc hp.hs (by simp only [slotOff]; omega)
    refine WP.block_cons_iff.mpr ⟨_, store32_exec hout, WP.block_nil ?_⟩
    rw [ea_at, u.other _ (by decide), h.rsi, u.gpr, u.mem]
    have e : ((V s₀)[n].setWidth 64).setWidth 32 = (V s₀)[n] := by simp
    rw [e]
    refine ⟨fun k hk hkn => ?_, fun k hk h12 hkn => ?_, ?_, u.rd.trans h.rd, u.wr.trans h.wr,
      (u.other _ (by decide)).trans h.rsi, (u.other _ (by decide)).trans h.rdi,
      (u.other _ (by decide)).trans h.rsp⟩
    · rw [u.other _ (wreg_ne k hk).1]; exact h.regs k hk (by omega)
    · by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [readW_writeW_off _ _ _ (by omega) (by simp only [slotOff]; omega)
          (by simp only [slotOff]; omega) (by simp only [slotOff]; omega)]
        exact h.slots k hk h12 (by omega)
    · exact h.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by simp only [slotOff]; omega) (by simp only [slotOff]; omega))

/-! ## Adding the input and storing the result -/

/-- The finish invariant after `n` words: `b` holds `R[j] + V[j]` for the
words `j < n` and still `V[j]` for the others. -/
structure FI (s₀ : State) (R : Vector Word 16) (sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bufAt (bp s₀) (4 * j)) 32 =
    if j < n then R[j] + (V s₀)[j] else (V s₀)[j]
  regs : ∀ k (hk : k < 12), n ≤ k → s.gpr (wreg k) = (R[k]'(by omega)).setWidth 64
  frame : Frame [bR (bp s₀)] sB.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsi : s.gpr .rsi = sp s₀
  rdi : s.gpr .rdi = bp s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {sB : State}
    (hsl : ∀ k (hk : k < 16), 12 ≤ k → sB.mem.readW (bufAt (sp s₀) (slotOff k)) 32 = R[k])
    {n : Nat} (hn : n < 16) {s : State} (h : FI s₀ R sB n s) :
    WP isa (.block (finishWord n)) s (FI s₀ R sB (n + 1)) := by
  have hb : readSrc32 s (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
    rw [mem_read (by rw [h.rdi, h.rd, h.wr]; exact in_b hp.hb (by omega)), h.rdi, h.out n hn]
    simp
  /- After the new sum is stored, the invariant holds. -/
  have fin : ∀ s' : State, s'.mem = s.mem.writeW (bufAt (bp s₀) (4 * n)) (R[n] + (V s₀)[n]) →
      (∀ k (hk : k < 12), n < k → s'.gpr (wreg k) = s.gpr (wreg k)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.gpr .rsi = s.gpr .rsi → s'.gpr .rdi = s.gpr .rdi →
      s'.gpr .rsp = s.gpr .rsp → FI s₀ R sB (n + 1) s' := by
    intro s' hm hg hrd hwr hrsi hrdi hrsp
    refine ⟨fun j hj => ?_, fun k hk hkn => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr,
      hrsi.trans h.rsi, hrdi.trans h.rdi, hrsp.trans h.rsp⟩
    · rw [hm]
      by_cases e : j = n
      · subst e; rw [Mem.readW_writeW_self32, ite_pos' (by omega)]
      · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega) (by omega), h.out j hj]
        by_cases hjn : j < n
        · rw [ite_pos' hjn, ite_pos' (by omega)]
        · rw [ite_neg' hjn, ite_neg' (by omega)]
    · rw [hg k hk (by omega)]; exact h.regs k hk (by omega)
    · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _
        (contains_off (by omega) (by omega))
  have hout : ∀ s' : State, s'.gpr .rdi = s.gpr .rdi → s'.wr = s.wr →
      InRegions s'.wr (s'.ea (at_ .rdi (4 * n))) 4 := by
    intro s' h1 h2
    rw [ea_at, h1, h2, h.rdi, h.wr]; exact out_b hp.hb (by omega)
  unfold finishWord
  split
  · rename_i hn12
    have ne := wreg_ne n hn12
    refine wp_cons (add32_upd (d := wreg n) hb) fun s' u => ?_
    refine WP.block_cons_iff.mpr ⟨_, store32_exec (hout s' (u.other _ ne.2.2.1.symm) u.wr),
      WP.block_nil (fin _ ?_ ?_ u.rd u.wr (u.other _ ne.2.1.symm) (u.other _ ne.2.2.1.symm)
        (u.other _ ne.2.2.2.symm))⟩
    · simp only [ea_at, u.other _ ne.2.2.1.symm, h.rdi, u.gpr, u.mem, h.regs n hn12 (Nat.le_refl _)]
      simp [bufAt]
    · intro k hk hkn
      exact u.other _ fun e => by have := wreg_inj k hk n hn12 e; omega
  · rename_i hn12
    have hsl' : readSrc32 s (.mem (at_ .rsi (slotOff n))) = some R[n] := by
      rw [mem_read (by rw [h.rsi, h.rd, h.wr]; exact in_sc hp.hs (by simp only [slotOff]; omega)),
        h.rsi, read_sc hp h.frame (by simp only [slotOff]; omega) (by decide), hsl n hn (by omega)]
    refine wp_cons (mov32_upd (d := .rax) hsl') fun s₁ u₁ => ?_
    have hb₁ : readSrc32 s₁ (.mem (at_ .rdi (4 * n))) = some (V s₀)[n] := by
      have hin : InRegions (s₁.rd ++ s₁.wr) (bufAt (s₁.gpr .rdi) (4 * n)) 4 := by
        rw [u₁.other _ (by decide), h.rdi, u₁.rd, u₁.wr, h.rd, h.wr]
        exact in_b hp.hb (by omega)
      rw [mem_read hin, u₁.other _ (by decide), h.rdi, u₁.mem, h.out n hn]
      simp
    refine wp_cons (add32_upd (d := .rax) hb₁) fun s₂ u₂ => ?_
    have e1 : s₂.gpr .rdi = s.gpr .rdi := (u₂.other _ (by decide)).trans (u₁.other _ (by decide))
    refine WP.block_cons_iff.mpr ⟨_, store32_exec (hout s₂ e1 (u₂.wr.trans u₁.wr)),
      WP.block_nil (fin _ ?_ ?_ (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr)
        ((u₂.other _ (by decide)).trans (u₁.other _ (by decide))) e1
        ((u₂.other _ (by decide)).trans (u₁.other _ (by decide))))⟩
    · simp only [ea_at, e1, h.rdi, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem]
      simp [bufAt]
    · intro k hk _
      rw [u₂.other _ (wreg_ne k hk).1, u₁.other _ (wreg_ne k hk).1]

end VG.Proof.Scrypt.X86_64
