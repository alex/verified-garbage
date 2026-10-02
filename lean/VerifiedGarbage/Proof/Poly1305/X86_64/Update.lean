import VerifiedGarbage.Proof.Poly1305.X86_64.Buffer
import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# Poly1305 on x86-64: `update`, up to the call

The contract `update` is proven against, and its code up to the call of
`vg_poly1305_blocks` (`updatePre`): saving the caller's registers in
`scratch`, filling the buffer and absorbing it once full, and setting up the
call.
-/

open VG.PowLit

namespace VG.Proof.Poly1305

open Spec.Poly1305 (bytesAt Buffered)

open VG.X86_64 in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len:
usize, scratch: *mut [u64; 16])`: only `count mod 16`, the number of bytes
buffered, matters. The call of `vg_poly1305_blocks` uses the 24 bytes of stack
below the return address (its return address, and up to 16 bytes for its own
calls, see `BlocksImpl`). -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 128⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : Addr := s₀.gpr .rdx
abbrev dl : Nat := (s₀.gpr .rcx).toNat
abbrev dR : Region := ⟨dp s₀, dl s₀⟩
/-- The number of bytes buffered. -/
abbrev kb : Nat := (s₀.gpr .rsi).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kb s₀)
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c
/-- The working space. -/
abbrev scr : Addr := s₀.gpr .r8
abbrev scR : Region := ⟨scr s₀, 128⟩
/-- The stack below the return address that the call uses. -/
abbrev stkR : Region := ⟨s₀.gpr .rsp - 24, 24⟩
end

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [sR (st s₀), scR s₀]
  st_sc : (sR (st s₀)).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (sR (st s₀))
  d_sc : (dR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  ret_sc : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (sR (st s₀))
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_sc : (stkR s₀).Disjoint (scR s₀)
  nowrap : (dp s₀).toNat + dl s₀ ≤ 2 ^ 64

theorem UPre.of (s₀ : State) (h : Proof.Poly1305.updateX86_64.pre s₀) : UPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by decide)

theorem rcx_eq (s₀ : State) : s₀.gpr .rcx = BitVec.ofNat 64 (dl s₀) := by simp

theorem dR_contains (s₀ : State) {i n : Nat} (h : i + n ≤ dl s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 i) n := by
  have := dl_lt s₀
  exact Offset.contains_base _ h (by omega_using [h, this])

theorem UPre.st_in {s₀ : State} (hp : UPre s₀) : sR (st s₀) ∈ s₀.wr := by
  rw [hp.wr]; exact List.mem_cons_self

theorem UPre.sc_in {s₀ : State} (hp : UPre s₀) : scR s₀ ∈ s₀.wr := by
  rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The accumulator and the key: what `Repr` reads. -/
abbrev rpR (st : Addr) : Region := ⟨st, 56⟩

theorem rpR_sub (st : Addr) : Region.Sub (rpR st) (sR st) := by
  have := Offset.sub_base st (d := 0) (n := 56) (k := 128) (by decide)
  rwa [BitVec.add_zero] at this

theorem rpR_bfR (st : Addr) : (rpR st).Disjoint (bfR st) := by
  simp only [bfR, off, ofInt_natCast]
  exact (Offset.disjoint_base st (d := 56) (n := 16) (k := 56) (by decide) (by decide)).symm

/-- A state represents the same message after writes outside its first 56
bytes. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (rpR p).Disjoint r) {key msg : List Byte} (h : Repr m p key msg) :
    Repr m' p key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  have s₁ : Region.Sub ⟨p + 24, 32⟩ (rpR p) := by
    have := Offset.sub_base p (d := 24) (n := 32) (k := 56) (by decide); exact this
  have s₂ : Region.Sub ⟨p, 24⟩ (rpR p) := by
    have := Offset.sub_base p (d := 0) (n := 24) (k := 56) (by decide)
    rwa [BitVec.add_zero] at this
  refine ⟨h1, ?_, ?_⟩
  · rw [Poly1305.bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₁) (by decide), h2]
  · rw [Poly1305.bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₂) (by decide), h3]

/-! ## The saved registers -/

theorem savedS_bound : ∀ q ∈ savedS, q.2 + 8 ≤ 48 := by decide

/-- The callee-saved registers of `s` are saved at `p` (in `scratch`). -/
abbrev SavedAt (p : Addr) (s : State) (m : Mem) : Prop := Spill.Saved m p s.gpr savedS

theorem SavedAt.frame {p : Addr} {s : State} {m m' : Mem} (h : SavedAt p s m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨p, 128⟩ : Region).Disjoint r) : SavedAt p s m' :=
  Spill.Saved.frame h hf fun q hq r hr =>
    (hd r hr).sub_left (Offset.sub_base p (by have := savedS_bound q hq; omega))

theorem saveS_ok (s : State) (hw : (⟨s.gpr .r8, 128⟩ : Region) ∈ s.wr) :
    WP isa (.block saveS) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨s.gpr .r8, 128⟩] s.mem s'.mem ∧ SavedAt (s.gpr .r8) s s'.mem :=
  WP.mono (Spill.save_ok .r8 savedS s fun q hq =>
      ⟨_, hw, Offset.contains_base _ (by have := savedS_bound q hq; omega)
        (by have := savedS_bound q hq; omega)⟩)
    fun s' ⟨hg, hrd, hwr, hm⟩ => ⟨hg, hrd, hwr,
      hm ▸ Spill.saveMem_frame_base _ _ _ _ (fun q hq => by have := savedS_bound q hq; omega) (by decide),
      hm ▸ Spill.saveMem_saved _ _ _ _ (by decide)⟩

/-! ## Invariants -/

/-- What holds from the prologue to the call. -/
structure UC (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r8 : s.gpr .r8 = scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt (scr s₀) s₀ s.mem

/-- After the prologue: only `scratch` is written. -/
structure Pre1 (s₀ : State) (s : State) : Prop extends UC s₀ s where
  frame : Frame [bfR (st s₀), scR s₀] s₀.mem s.mem
  rsi : s.gpr .rsi = dp s₀
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀) = Bf s₀

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (n : Nat) (s : State) : Prop extends UC s₀ s where
  frame : Frame [bfR (st s₀), scR s₀] s₀.mem s.mem
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - n)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀ + n)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀ + n) = Bf s₀ ++ Dt s₀ n

/-- With `c` bytes of data consumed, the memory `m` represents the message
on entry followed by `X`, with `Y` buffered (`Bf ++ Dt c = X ++ Y`); `Y` is
empty unless all the data is consumed. -/
def StOk (s₀ : State) (c : Nat) (m : Mem) : Prop :=
  ∃ X Y : List Byte, X.length % 16 = 0 ∧ Y.length < 16 ∧ Bf s₀ ++ Dt s₀ c = X ++ Y ∧
    (Y = [] ∨ c = dl s₀) ∧ bytesAt m (off (st s₀) 56) Y.length = Y ∧
    ∀ key W, Repr s₀.mem (st s₀) key W → Repr m (st s₀) key (W ++ X)

/-- After the buffer: `c` bytes of data consumed. -/
structure AfterFill (s₀ : State) (c : Nat) (s : State) : Prop extends UC s₀ s where
  frame : Frame [sR (st s₀), scR s₀] s₀.mem s.mem
  c_le : c ≤ dl s₀
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 c
  rcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - c)
  st : StOk s₀ c s.mem

/-- A state that differs from `s` only in the flags. -/
def FlagsOnly (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem UC.of_regs {s₀ s s' : State} (h : UC s₀ s)
    (hg : ∀ r ∈ [Reg.rdi, .rsp, .r8], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : UC s₀ s' where
  rdi := by rw [hg _ (by simp)]; exact h.rdi
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  r8 := by rw [hg _ (by simp)]; exact h.r8
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  saved := by rw [hm]; exact h.saved

theorem UC.flags {s₀ s s' : State} (h : UC s₀ s) (hf : FlagsOnly s s') : UC s₀ s' :=
  h.of_regs (fun r _ => by rw [hf.1]) hf.2.1 hf.2.2.1 hf.2.2.2

theorem UC.in_st {s₀ : State} (hp : UPre s₀) {s : State} (h : UC s₀ s) : sR (s.gpr .rdi) ∈ s.wr := by
  rw [h.wr, h.rdi]; exact hp.st_in

/-- Bytes of data, read from memory written only in the state and `scratch`. -/
theorem UPre.data {s₀ : State} (hp : UPre s₀) {rs : List Region} {m : Mem} (hf : Frame rs s₀.mem m)
    (hrs : ∀ r ∈ rs, Region.Sub r (sR (st s₀)) ∨ r = scR s₀) {i : Nat} (hi : i < dl s₀) :
    m (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  hf.bytes (R := dR s₀) (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hp.d_st.sub_right h
    · exact hp.d_sc) (show dl s₀ ≤ 2 ^ 64 by have := dl_lt s₀; omega_using [this]) hi

theorem bfR_sub_sR (st : Addr) : Region.Sub (bfR st) (sR st) := by
  simp only [bfR, off, ofInt_natCast]; exact Offset.sub_base st (by decide)

/-- The source of a copy from the data. -/
theorem UPre.srcOk {s₀ : State} (hp : UPre s₀) {s : State} (hc : UC s₀ s)
    (hf : Frame [bfR (st s₀), scR s₀] s₀.mem s.mem) {c n : Nat}
    (h : c + n ≤ dl s₀) : SrcOk s s₀.mem (dp s₀ + BitVec.ofNat 64 c) n := by
  intro i hi
  have e : dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i = dp s₀ + BitVec.ofNat 64 (c + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine ⟨⟨dR s₀, by rw [hc.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    dR_contains s₀ (by omega_using [h, hi])⟩, fun hb => ?_,
    hp.data hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (bfR_sub_sR _)
      · exact .inr rfl) (by omega_using [h, hi])⟩
  rw [hc.rdi] at hb
  exact hp.d_st _ (dR_contains s₀ (by omega_using [h, hi])) (bfR_sub_sR _ _ hb)

/-! ## Prologue -/

set_option simprocs false in
theorem kInit_ok (s : State) :
    WP isa (.block [.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15), .mov .rsi (.reg .rdx),
      .alu .test .r12 (.reg .r12)]) s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) ∧ s'.gpr .rsi = s.gpr .rdx ∧
      s'.zf = some (BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) &&&
        BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) == 0) ∧
      Keeps [.r12, .rsi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', and15]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem uprologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (saveS ++ ([.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15),
      .mov .rsi (.reg .rdx), .alu .test .r12 (.reg .r12)] : List Instr))) s₀ fun s =>
      Pre1 s₀ s ∧ s.gpr .rcx = s₀.gpr .rcx ∧
        s.zf = some (BitVec.ofNat 64 (kb s₀) &&& BitVec.ofNat 64 (kb s₀) == 0) := by
  refine WP.block_append (WP.mono (saveS_ok s₀ hp.sc_in) fun s₁ ⟨g₁, rd₁, wr₁, f₁, sv₁⟩ => ?_)
  refine WP.mono (kInit_ok s₁) fun s₂ ⟨c12, csi, cz, k₂⟩ => ?_
  have g : ∀ r, r ∉ [Reg.r12, .rsi] → s₂.gpr r = s₀.gpr r := fun r hr => by rw [k₂.1 r hr, g₁]
  have hm₂ : s₂.mem = s₁.mem := k₂.2.1
  have hkb := kb_lt s₀
  refine ⟨⟨⟨g .rdi (by decide), g .rsp (by decide), g .r8 (by decide), by rw [k₂.2.2.1, rd₁],
    by rw [k₂.2.2.2, wr₁], by rw [hm₂]; exact sv₁⟩, ?_, by rw [csi, g₁], by rw [c12, g₁], ?_⟩,
    g .rcx (by decide), by rw [cz, g₁]⟩
  · rw [hm₂]; exact f₁.mono (by simp)
  · rw [hm₂]
    refine Poly1305.bytesAt_frame f₁ (fun r hr => ?_) (by omega_using [hkb])
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_sc.sub_left (sub_sR _ (by omega_using [hkb])))

/-- Nothing buffered: the state already represents the message's whole blocks. -/
theorem Pre1.after {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s)
    (hrcx : s.gpr .rcx = s₀.gpr .rcx) (hk : kb s₀ = 0) : AfterFill s₀ 0 s :=
  { h.toUC with
    frame := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, bfR_sub_sR _⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    c_le := Nat.zero_le _
    rsi := by rw [h.rsi]; simp
    rcx := by rw [hrcx]; simp
    st := ⟨[], [], rfl, by decide, by simp only [Bf, Dt, hk]; rfl, .inl rfl, rfl,
      fun key W hr => by
        rw [List.append_nil]
        refine repr_frame h.frame (fun r hr' => ?_) hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · exact rpR_bfR _
        · exact hp.st_sc.sub_left (rpR_sub _)⟩ }

/-! ## Filling the buffer -/

/-- `Pre1` is kept by changes to `rax`, `rcx` and the flags. -/
theorem Pre1.of_regs {s₀ s s' : State} (h : Pre1 s₀ s) (hg : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pre1 s₀ s' :=
  { h.toUC.of_regs (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) hm hrd hwr with
    frame := by rw [hm]; exact h.frame
    rsi := by rw [hg _ (by decide) (by decide)]; exact h.rsi
    r12 := by rw [hg _ (by decide) (by decide)]; exact h.r12
    buf := by rw [hm]; exact h.buf }

/-- The number of bytes to copy, `n = min(16 - kb, dl)`, into `rax`, and
`dl - n` into `rcx`. -/
theorem count_ok {s₀ : State} {s : State} (h : Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa count s fun s' =>
      Pre1 s₀ s' ∧ s'.gpr .rax = BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀)) ∧
        s'.gpr .rcx = BitVec.ofNat 64 (dl s₀ - min (16 - kb s₀) (dl s₀)) ∧
        s'.zf = some (decide (min (16 - kb s₀) (dl s₀) = 0)) := by
  have hkl := kb_lt s₀
  have hdl := dl_lt s₀
  have e16 : BitVec.setWidth 64 (16 : BitVec 32) - BitVec.ofNat 64 (kb s₀) =
      BitVec.ofNat 64 (16 - kb s₀) := by
    rw [show BitVec.setWidth 64 (16 : BitVec 32) = BitVec.ofNat 64 16 by decide, sub_ofNat (by omega_using [hkl])]
  refine WP.seq (wp_mov32i fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (16 - kb s₀) := by
    rw [u₂.gpr, u₁.other .r12 (by decide), h.r12, u₁.gpr, e16]
  have hrcx₂ : s₂.gpr .rcx = s₀.gpr .rcx := by
    rw [u₂.other .rcx (by decide), u₁.other .rcx (by decide), hrcx]
  have hrax₃ : s₃.gpr .rax = BitVec.ofNat 64 (16 - kb s₀) := by rw [g₃, hrax₂]
  have hrcx₃ : s₃.gpr .rcx = s₀.gpr .rcx := by rw [g₃, hrcx₂]
  have hP₃ : Pre1 s₀ s₃ := h.of_regs (fun r h1 _ => by rw [g₃, u₂.other r h1, u₁.other r h1])
    (by rw [m₃, u₂.mem, u₁.mem]) (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  -- `rax = n`.
  refine WP.seq (WP.mono (Q := fun s₄ : State => Pre1 s₀ s₄ ∧ s₄.gpr .rcx = s₀.gpr .rcx ∧
      s₄.gpr .rax = BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀))) ?_ fun s₄ ⟨hP₄, hrcx₄, hrax₄⟩ => ?_)
  · refine WP.ite (decide (dl s₀ < 16 - kb s₀)) (by
      simp only [eval, cf₃, hrcx₂, hrax₂, toNat_ofNat_lt (show 16 - kb s₀ < 2 ^ 64 by omega_using [hkl])])
      (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₄ u₄ => WP.block_nil ⟨hP₃.of_regs (fun r h1 _ => u₄.other r h1) u₄.mem u₄.rd u₄.wr,
        by rw [u₄.other _ (by decide), hrcx₃], ?_⟩
      simp only [decide_eq_true_eq] at hb
      rw [u₄.gpr, hrcx₃, Nat.min_eq_right (by omega_using [hb]), rcx_eq]
    · refine WP.block_nil ⟨hP₃, hrcx₃, ?_⟩
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      rw [hrax₃, Nat.min_eq_left hb]
  · refine wp_sub fun s₅ u₅ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_
    have hg : ∀ r, r ≠ .rcx → s₆.gpr r = s₄.gpr r := fun r hr => by rw [g₆, u₅.other r hr]
    refine ⟨hP₄.of_regs (fun r _ h2 => hg r h2) (by rw [m₆, u₅.mem]) (by rw [rd₆, u₅.rd])
      (by rw [wr₆, u₅.wr]), by rw [hg _ (by decide)]; exact hrax₄, ?_, ?_⟩
    · rw [g₆, u₅.gpr, hrcx₄, hrax₄, rcx_eq, sub_ofNat (by omega_using [])]
    · rw [z₆, u₅.other _ (by decide), hrax₄, BitVec.and_self, ofNat_beq_zero (by omega_using [hdl])]

theorem copyFill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s) {n : Nat} (hn : n ≤ dl s₀)
    (hn' : kb s₀ + n ≤ 16) (hrax : s.gpr .rax = BitVec.ofNat 64 n)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - n)) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) copyIn) s (Filled s₀ n) := by
  refine WP.ite (decide (n = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil { h.toUC with
      frame := h.frame, n_le := hn, n_le' := hn', rsi := by rw [h.rsi]; simp, rcx := hrcx,
      r12 := by rw [h.r12]; simp
      buf := by rw [Nat.add_zero, h.buf]; simp [Dt, bytesAt] }
  · simp only [decide_eq_false_iff_not] at h0
    have hsrc := hp.srcOk h.toUC h.frame (c := 0) (n := n) (by omega_using [hn])
    refine WP.mono (copy_ok (j0 := kb s₀) (by omega_using [hn']) (by omega_using [h0]) (h.toUC.in_st hp)
      hsrc (by rw [h.rsi]; simp) (by rw [h.r12]) hrax) fun s' hc => ?_
    have hk : ∀ r ∈ [Reg.rdi, .rsp, .r8], s'.gpr r = s.gpr r := fun r hr => hc.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    have hf : Frame [bfR (st s₀)] s.mem s'.mem := by rw [← h.rdi]; exact hc.frame (by omega_using [hn'])
    refine { rdi := by rw [hk _ (by simp)]; exact h.rdi
             rsp := by rw [hk _ (by simp)]; exact h.rsp
             r8 := by rw [hk _ (by simp)]; exact h.r8
             rd := hc.rd.trans h.rd
             wr := hc.wr.trans h.wr
             saved := h.saved.frame hf (fun r hr => by
               simp only [List.mem_singleton] at hr; subst hr
               exact hp.st_sc.symm.sub_right (bfR_sub_sR _))
             frame := h.frame.trans (hf.mono (by simp))
             n_le := hn, n_le' := hn', rsi := by rw [hc.rsi]; simp
             rcx := by rw [hc.keep _ (by decide) (by decide) (by decide) (by decide), hrcx]
             r12 := hc.r12
             buf := ?_ }
    have hb := hc.buf (by omega_using [hn'])
    rw [h.rdi, h.buf] at hb
    rw [hb]
    simp [Dt]

/-! ## Absorbing the full buffer -/

/-- The memory after keeping `a, b, c` in the state's working space. -/
def stash (m : Mem) (st : Addr) (a b c : BitVec 64) : Mem :=
  ((m.writeW (off st 72) a).writeW (off st 80) b).writeW (off st 88) c

set_option simprocs false in
theorem stash_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block [.store (at_ .rdi 72) .rsi, .store (at_ .rdi 80) .rcx, .store (at_ .rdi 88) .r8]) s
      fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = stash s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r8) := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 72 (by decide); have o1 := o 80 (by decide); have o2 := o 88 (by decide)
  simp only [off] at o0 o1 o2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, o0, o1, o2, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

theorem stash_frame (m : Mem) (st : Addr) (a b c : BitVec 64) : Frame [wR st] m (stash m st a b c) := by
  have k : ∀ d, 56 ≤ d → d + 8 ≤ 128 → (wR st).Contains (off st d) (64 / 8) :=
    fun d h₁ h₂ => wR_contains st h₁ h₂
  exact (((Frame.refl _ _).writeW List.mem_cons_self _ (k 72 (by decide) (by decide))).writeW
    List.mem_cons_self _ (k 80 (by decide) (by decide))).writeW List.mem_cons_self _ (k 88 (by decide) (by decide))

theorem stash_low (m : Mem) (st : Addr) (a b c : BitVec 64) {d : Nat} (hd : d + 8 ≤ 72) :
    (stash m st a b c).readW (off st d) 64 = m.readW (off st d) 64 := by
  simp only [stash]
  rw [readW_writeW_off _ _ _ (by omega_using [hd]) (by decide) (by omega_using [hd]),
    readW_writeW_off _ _ _ (by omega_using [hd]) (by decide) (by omega_using [hd]),
    readW_writeW_off _ _ _ (by omega_using [hd]) (by decide) (by omega_using [hd])]

/-- The buffer is not where `stash` writes. -/
theorem stash_buf (m : Mem) (st : Addr) (a b c : BitVec 64) :
    bytesAt (stash m st a b c) (off st 56) 16 = bytesAt m (off st 56) 16 := by
  have f : Frame [⟨off st 72, 24⟩] m (stash m st a b c) := by
    have k : ∀ d, 72 ≤ d → d + 8 ≤ 96 → (⟨off st 72, 24⟩ : Region).Contains (off st d) (64 / 8) := by
      intro d h₁ h₂
      simp only [off, ofInt_natCast]; exact Offset.contains st h₁ (by omega_using [h₂]) (by decide)
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (k 72 (by decide) (by decide))).writeW
      List.mem_cons_self _ (k 80 (by decide) (by decide))).writeW List.mem_cons_self _
      (k 88 (by decide) (by decide))
  refine Poly1305.bytesAt_frame f (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  simp only [off, ofInt_natCast]
  exact Offset.disjoint st (by decide) (by decide) (by decide)

set_option simprocs false in
/-- Storing `h` and loading back `rsi`, `rcx` and `r8`. -/
theorem storeReload_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp,
      .mov .rsi (.mem (at_ .rdi 72)), .mov .rcx (.mem (at_ .rdi 80)), .mov .r8 (.mem (at_ .rdi 88))]) s
      fun s' =>
      s'.mem = storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rsi = (storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)).readW
        (off (s.gpr .rdi) 72) 64 ∧
      s'.gpr .rcx = (storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)).readW
        (off (s.gpr .rdi) 80) 64 ∧
      s'.gpr .r8 = (storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)).readW
        (off (s.gpr .rdi) 88) 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  simp only [off] at o0 o8 o16 i0 i1 i2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.store64, State.load64, State.setReg, o0, o8, o16, i0, i1, i2,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_, ?_⟩
  · simp only [h1, h2, h3, ite_false]
  · trivial

theorem absorbBuf_eq : absorbBuf =
    ([.store (at_ .rdi 72) .rsi, .store (at_ .rdi 80) .rcx, .store (at_ .rdi 88) .r8] : List Instr) ++
    (setup ++ (absorbAt .rdi 56 1 ++ (reduce ++
    ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp,
      .mov .rsi (.mem (at_ .rdi 72)), .mov .rcx (.mem (at_ .rdi 80)), .mov .r8 (.mem (at_ .rdi 88))] :
      List Instr)))) := by
  simp only [absorbBuf, List.append_assoc, List.cons_append, List.nil_append]

theorem off_disj_bfR (st : Addr) {d : Nat} (hd : d + 8 ≤ 56) :
    (⟨off st d, 8⟩ : Region).Disjoint (bfR st) := by
  simp only [bfR, off, ofInt_natCast]
  exact Offset.disjoint st (by omega_using [hd]) (by omega_using [hd]) (by decide)

/-- A word of the accumulator or the key, unchanged since entry. -/
theorem Filled.low {s₀ : State} (hp : UPre s₀) {n : Nat} {s : State} (h : Filled s₀ n s) {d : Nat}
    (hd : d + 8 ≤ 56) : s.mem.readW (off (st s₀) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
  refine h.frame.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact off_disj_bfR _ hd
  · exact hp.st_sc.sub_left (sub_sR _ (by omega_using [hd]))

theorem hR_sub_sR (st : Addr) : Region.Sub (hR st) (sR st) := by
  have := sub_sR st (d := 0) (n := 24) (by decide)
  rwa [off_eq, BitVec.add_zero] at this

theorem wR_sub_sR (st : Addr) : Region.Sub (wR st) (sR st) := sub_sR st (d := 56) (n := 72) (by decide)

theorem hR_wR_sub (st : Addr) (R : Region) :
    ∀ r ∈ [hR st, wR st], ∃ r' ∈ [sR st, R], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  refine ⟨sR st, List.mem_cons_self, ?_⟩
  rcases hr with rfl | rfl
  · exact hR_sub_sR st
  · exact wR_sub_sR st

theorem bfR_sc_sub (st : Addr) (R : Region) :
    ∀ r ∈ [bfR st, R], ∃ r' ∈ [sR st, R], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, bfR_sub_sR _⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- Absorbing the full buffer. -/
theorem absorbFull_ok {s₀ : State} (hp : UPre s₀) {s : State} {n : Nat} (h : Filled s₀ n s)
    (hfull : kb s₀ + n = 16) : WP isa (.block absorbBuf) s (AfterFill s₀ n) := by
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  have hw : sR (s.gpr .rdi) ∈ s.wr := h.toUC.in_st hp
  rw [absorbBuf_eq]
  refine WP.block_append (WP.mono (stash_ok s hw) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hw₁ : sR (s₁.gpr .rdi) ∈ s₁.wr := by rw [g₁, wr₁]; exact hw
  refine WP.block_append (WP.mono (setup_ok s₁ (List.mem_append_right _ hw₁))
    fun s₂ ⟨e8, e9, e10, e11, e12, e13, k₂⟩ => ?_)
  have low : ∀ d, d + 8 ≤ 56 →
      s₁.mem.readW (off (s₁.gpr .rdi) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
    intro d hd
    rw [m₁, g₁, h.rdi, stash_low _ _ _ _ _ (by omega_using [hd]), h.low hp hd]
  rw [low 24 (by decide)] at e8
  rw [low 32 (by decide)] at e9
  replace e8 : s₂.gpr .r8 = R0 s₀ := e8
  replace e9 : s₂.gpr .r9 = R1 s₀ := e9
  rw [low 0 (by decide)] at e11
  rw [low 8 (by decide)] at e12
  rw [low 16 (by decide)] at e13
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [k₂.gpr' (r := .rdi), g₁, h.rdi]
  have hw₂ : sR (s₂.gpr .rdi) ∈ s₂.wr := by rw [k₂.2.2.2, k₂.gpr' (r := .rdi)]; exact hw₁
  refine WP.block_append (WP.mono (absorbBuf_ok s₂ (pad := 1) (Or.inr rfl) hw₂ (q := (R1 s₀).toNat / 4)
    (by rw [e8]; exact r0_lt _) (by rw [e9]; omega_using [hq]) (by omega_using [hq, hq'])
    (by rw [e10, e9])) fun s₃ ⟨ha, k₃⟩ => ?_)
  have rdi₃ : s₃.gpr .rdi = st s₀ := by rw [k₃.gpr' (r := .rdi), rdi₂]
  refine WP.block_append (WP.mono (reduce_ok s₃) fun s₄ ⟨hr, k₄⟩ => ?_)
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [k₄.gpr' (r := .rdi), rdi₃]
  have hw₄ : sR (s₄.gpr .rdi) ∈ s₄.wr := by rw [k₄.2.2.2, k₃.2.2.2, rdi₄, ← rdi₂]; exact hw₂
  refine WP.mono (storeReload_ok s₄ hw₄) fun s₅ ⟨m₅, rsi₅, rcx₅, r8₅, g₅, rd₅, wr₅⟩ => ?_
  have mem₄ : s₄.mem = stash s.mem (st s₀) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r8) := by
    rw [k₄.2.1, k₃.2.1, k₂.2.1, m₁, h.rdi]
  rw [rdi₄, mem₄] at m₅ rsi₅ rcx₅ r8₅
  rw [storeH_saved _ _ _ _ _ (by decide) (by decide)] at rsi₅ rcx₅ r8₅
  simp only [stash] at rsi₅ rcx₅ r8₅
  rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64] at rsi₅
  rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64] at rcx₅
  rw [Mem.readW_writeW_self64] at r8₅
  -- Registers.
  have rdi₅ : s₅.gpr .rdi = st s₀ := by rw [g₅ _ (by decide) (by decide) (by decide), rdi₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅ _ (by decide) (by decide) (by decide), k₄.gpr' (r := .rsp), k₃.gpr' (r := .rsp),
      k₂.gpr' (r := .rsp), g₁, h.rsp]
  -- Memory.
  have fs : Frame [hR (st s₀), wR (st s₀)] s.mem s₅.mem := by
    rw [m₅]; exact storeH_frame ((stash_frame _ _ _ _ _).mono (by simp)) _ _ _
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, rd₁, h.rd]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, wr₁, h.wr]
  have hf₅ : Frame [sR (st s₀), scR s₀] s₀.mem s₅.mem :=
    (h.frame.sub (bfR_sc_sub _ _)).trans (fs.sub (hR_wR_sub _ _))
  have hl : (Bf s₀ ++ Dt s₀ n).length = 16 := by
    simp only [List.length_append, Dt, Poly1305.length_bytesAt]; omega_using [hfull]
  refine { rdi := rdi₅, rsp := rsp₅, r8 := by rw [r8₅]; exact h.r8, rd := rd₅', wr := wr₅'
           saved := h.saved.frame fs (fun r hr => by
             obtain ⟨r', hr', hs⟩ := hR_wR_sub (st s₀) (scR s₀) r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
             rcases hr' with rfl | rfl
             · exact hp.st_sc.symm.sub_right hs
             · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
               rcases hr with rfl | rfl
               · exact hp.st_sc.symm.sub_right (hR_sub_sR _)
               · exact hp.st_sc.symm.sub_right (wR_sub_sR _))
           frame := hf₅
           c_le := h.n_le
           rsi := by rw [rsi₅]; exact h.rsi
           rcx := by rw [rcx₅]; exact h.rcx
           st := ⟨Bf s₀ ++ Dt s₀ n, [], by omega_using [hl], by decide, (List.append_nil _).symm, .inl rfl,
             rfl, fun key W hrep => ?_⟩ }
  -- The accumulator.
  obtain ⟨hlen, hkey, hacc⟩ := hrep
  have hH2 := H2_le ⟨hlen, hkey, hacc⟩
  have hb₂ : (s₂.gpr .rbp).toNat ≤ 4 := by rw [e13]; exact hH2
  obtain ⟨hv₃, hb₃⟩ := ha hb₂
  have hR4 := hr hb₃
  have hbuf : bytesAt s₂.mem (off (s₂.gpr .rdi) 56) 16 = Bf s₀ ++ Dt s₀ n := by
    rw [k₂.2.1, m₁, rdi₂, h.rdi, stash_buf, ← hfull, h.buf]
  have hkey₀ : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
  have hkey₅ : bytesAt s₅.mem (off (st s₀) 24) 32 = key := by
    rw [← hkey₀, key_frame fs]
    refine Poly1305.bytesAt_frame h.frame (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (kR_disjoint _ _ (List.mem_cons_of_mem _ List.mem_cons_self)).sub_right (bfR_sub_wR _)
    · exact hp.st_sc.sub_left (sub_sR _ (by decide))
  have hA : accumulate (Rn s₀) W = A0 s₀ := by rw [A0, hacc, ← hkey₀, clamp_key]
  have e : leNum (Bf s₀ ++ Dt s₀ n ++ [0x01]) = leNum (Bf s₀ ++ Dt s₀ n) + 2 ^ 128 * 1 := by
    rw [Poly1305.leNum_append, hl]; rfl
  have h2 : hval s₂ = A0 s₀ := by simp only [hval, e11, e12, e13]; rw [A0, leNum_acc]
  refine ⟨by rw [List.length_append]; omega_using [hlen, hl], by rw [← off_24]; exact hkey₅, ?_⟩
  rw [m₅, storeH_acc, ← hkey₀, clamp_key, Poly1305.accumulate_append hlen, hA,
    Poly1305.absorbAll_block (by rw [hl]; decide) (by rw [hl]), e]
  change hval s₄ = _
  rw [hR4, hv₃, hbuf, h2, e8, e9, show (1 : BitVec 32).toNat = 1 from rfl, mod_step (X := A0 s₀) rfl,
    Nat.mod_mod]

theorem Filled.flags {s₀ s s' : State} {n : Nat} (h : Filled s₀ n s) (hf : FlagsOnly s s') :
    Filled s₀ n s' :=
  { h.toUC.flags hf with
    frame := by rw [hf.2.1]; exact h.frame
    n_le := h.n_le, n_le' := h.n_le', rsi := by rw [hf.1]; exact h.rsi, rcx := by rw [hf.1]; exact h.rcx,
    r12 := by rw [hf.1]; exact h.r12, buf := by rw [hf.2.1]; exact h.buf }

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa fill s fun s' => ∃ c, AfterFill s₀ c s' := by
  have hkl := kb_lt s₀
  have hdl := dl_lt s₀
  have hn : min (16 - kb s₀) (dl s₀) ≤ dl s₀ := Nat.min_le_right _ _
  have hn' : kb s₀ + min (16 - kb s₀) (dl s₀) ≤ 16 := by
    have := Nat.min_le_left (16 - kb s₀) (dl s₀); omega_using [hkl, this]
  refine WP.seq (WP.mono (count_ok h hrcx) fun s₁ ⟨h₁, hrax₁, hrcx₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (copyFill_ok hp h₁ hn hn' hrax₁ hrcx₁ hz₁) fun s₂ h₂ => ?_)
  refine WP.seq (wp_cmpi fun s₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_)
  have hf : FlagsOnly s₂ s₃ := ⟨g₃, m₃, rd₃, wr₃⟩
  have h₃ := h₂.flags hf
  refine WP.ite (decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16))
    (by simp only [eval, z₃, h₂.r12, se16']
        rw [sub_beq (a := kb s₀ + min (16 - kb s₀) (dl s₀)) (b := 16) (by omega_using [hn']) (by decide)])
    (fun hfull => ?_) (fun hnf => ?_)
  · exact WP.mono (absorbFull_ok hp h₃ (by simpa using hfull)) fun s' h' => ⟨_, h'⟩
  · simp only [decide_eq_false_iff_not] at hnf
    have hnd : min (16 - kb s₀) (dl s₀) = dl s₀ := by omega_using [hkl, hn, hn', hnf]
    refine WP.block_nil ⟨dl s₀, { h₃.toUC with
      frame := h₃.frame.sub (bfR_sc_sub _ _)
      c_le := Nat.le_refl _
      rsi := by rw [h₃.rsi, hnd]
      rcx := by rw [h₃.rcx, hnd]
      st := ⟨[], Bf s₀ ++ Dt s₀ (dl s₀), rfl, ?_, rfl, .inr rfl, ?_, fun key W hr => ?_⟩ }⟩
    · simp only [List.length_append, Dt, Poly1305.length_bytesAt]; omega_using [hn', hnf, hnd]
    · have hb := h₃.buf
      rw [hnd] at hb
      simp only [List.length_append, Dt, Poly1305.length_bytesAt]
      exact hb
    · rw [List.append_nil]
      refine repr_frame h₃.frame (fun r hr' => ?_) hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact rpR_bfR _
      · exact hp.st_sc.sub_left (rpR_sub _)

/-! ## The arguments of the call -/

theorem wp_shr4 {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d >>> 4) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d 4 :: is)) s Q :=
  WP.cons rfl (k _ (Upd.withFlags _ _ _ _ _ _ _))

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) :
    BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by omega_using [h]),
    Nat.shiftRight_eq_div_pow]

/-- Before the call, or none: `c` bytes of data consumed, and what is kept across it. -/
structure Ready (s₀ : State) (c : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rbx : s.gpr .rbx = st s₀
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 c
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (dl s₀ - c)
  rdx : s.gpr .rdx = BitVec.ofNat 64 ((dl s₀ - c) / 16)
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), scR s₀] s₀.mem s.mem
  saved : SavedAt (scr s₀) s₀ s.mem
  c_le : c ≤ dl s₀
  cf : s.cf = some (decide (dl s₀ - c < 16))
  st : StOk s₀ c s.mem

theorem callArgs_ok {s₀ : State} {c : Nat} {s : State} (h : AfterFill s₀ c s) :
    WP isa (.block callArgs) s (Ready s₀ c) := by
  have hdl := dl_lt s₀
  unfold callArgs
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_shr4 fun s₆ u₆ => wp_cmpi fun s₇ g₇ m₇ rd₇ wr₇ cf₇ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .rdx → s₇.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [g₇, u₆.other r h5, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have rcx₅ : s₅.gpr .rcx = s.gpr .rcx := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  have mem₇ : s₇.mem = s.mem := by rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact {
    rdi := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rdi
    rbx := by
      rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact h.rdi
    rsi := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rsi
    rbp := by
      rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact h.rsi
    r12 := by
      rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact h.rcx
    rdx := by
      rw [g₇, u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.rcx, shr4_ofNat (by omega_using [hdl])]
    r15 := by rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact h.r8
    rsp := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rsp
    rd := by rw [rd₇, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact h.rd
    wr := by rw [wr₇, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr
    frame := by rw [mem₇]; exact h.frame
    saved := by rw [mem₇]; exact h.saved
    c_le := h.c_le
    cf := by
      rw [cf₇, u₆.other _ (by decide), rcx₅, h.rcx, se16', toNat_ofNat_lt (by omega_using [hdl]),
        toNat_ofNat_lt (by decide)]
    st := by rw [mem₇]; exact h.st }

theorem updatePre_ok {s₀ : State} (hp : UPre s₀) :
    WP isa updatePre s₀ fun s => ∃ c, Ready s₀ c s := by
  refine WP.seq (WP.mono (uprologue_ok hp) fun s₁ ⟨h₁, hrcx, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ c, AfterFill s₀ c s) ?_ fun s₂ ⟨c, h₂⟩ =>
    WP.mono (callArgs_ok h₂) fun s₃ h₃ => ⟨c, h₃⟩)
  refine WP.ite (BitVec.ofNat 64 (kb s₀) &&& BitVec.ofNat 64 (kb s₀) == 0) (by simp [eval, hz])
    (fun h => ?_) (fun _ => fill_ok hp h₁ hrcx)
  rw [BitVec.and_self, ofNat_beq_zero (by have := kb_lt s₀; omega_using [this])] at h
  simp only [decide_eq_true_eq] at h
  exact WP.block_nil ⟨0, h₁.after hp hrcx h⟩

end VG.Proof.Poly1305.X86_64
