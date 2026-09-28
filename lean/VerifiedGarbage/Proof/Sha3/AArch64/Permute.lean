import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Sha3.AArch64.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Contract

/-!
# Keccak-f[1600] on AArch64: the whole function

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Sha3.X86_64`), with one round per iteration: the
AArch64 constant-time analysis tracks only which registers are public, so
swapping the pointers every round loses nothing.
-/

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev scr : Addr := s₀.gpr .x1
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev A₀ : KState := stateAt s₀.mem (st s₀)

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : Addr := if r % 2 = 0 then st s₀ else scr s₀
def oth (r : Nat) : Addr := if r % 2 = 0 then scr s₀ else st s₀

/-- Scratch offset `d`. -/
abbrev off (d : Nat) : Addr := scr s₀ + BitVec.ofNat 64 d

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem oth_succ (s₀ : State) (r : Nat) : oth s₀ (r + 1) = cur s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega

theorem cur_cases (s₀ : State) (r : Nat) :
    (cur s₀ r = st s₀ ∧ oth s₀ r = scr s₀) ∨ (cur s₀ r = scr s₀ ∧ oth s₀ r = st s₀) := by
  simp only [cur, oth]; split
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_wr {R : Region} (hR : R = stR s₀ ∨ R = scrR s₀) {a : Addr} {n : Nat}
    (hc : R.Contains a n) : InRegions s₀.wr a n := by
  rw [h.wr]; rcases hR with rfl | rfl
  · exact ⟨_, by simp, hc⟩
  · exact ⟨_, by simp, hc⟩

theorem in_all {a : Addr} {n : Nat} (hw : InRegions s₀.wr a n) : InRegions (s₀.rd ++ s₀.wr) a n := by
  rw [h.rd]; exact hw

theorem lane_in {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {i : Nat} (hi : i < 25) :
    InRegions s₀.wr (laneAddr p i) 8 := by
  rcases hp with rfl | rfl
  · exact h.in_wr (.inl rfl) (lane_contains _ hi)
  · exact h.in_wr (.inr rfl) (contains_offset (by omega) (by omega))

theorem off_in {d : Nat} (hd : d + 8 ≤ 512) : InRegions s₀.wr (off s₀ d) 8 :=
  h.in_wr (.inr rfl) (contains_offset hd (by omega))

/-- The first 200 bytes of the scratch space are disjoint from the state. -/
theorem st_scr200 : (stR s₀).Disjoint ⟨scr s₀, 200⟩ :=
  h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The state and the second state are disjoint from every later scratch offset. -/
theorem region_off {p : Addr} (hp : p = st s₀ ∨ p = scr s₀) {d n : Nat} (hd : 200 ≤ d)
    (hn : d + n ≤ 512) : Region.Disjoint ⟨p, 200⟩ ⟨off s₀ d, n⟩ := by
  rcases hp with rfl | rfl
  · exact h.st_scr.sub_right (sub_offset hn (by omega))
  · have := off_disjoint (scr s₀) (a := 0) (n := 200) (b := d) (k := n) (by omega) (by omega)
      (.inl hd)
    rwa [add_zero'] at this

theorem env (r : Nat) (hr : r < 24) :
    Env s₀.rd s₀.wr (cur s₀ r) (oth s₀ r) (off s₀ (200 + 8 * r)) := by
  have hc := cur_cases s₀ r
  have hcur : cur s₀ r = st s₀ ∨ cur s₀ r = scr s₀ := hc.imp (·.1) (·.1)
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine ⟨fun i hi => h.in_all (h.lane_in hcur hi), fun i hi => h.lane_in hoth hi,
    h.in_all (h.off_in (by omega)), ?_, h.region_off hoth (by omega) (by omega)⟩
  rcases hc with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂]
  · exact h.st_scr200.symm
  · exact h.st_scr200

end Pre

/-! ## The round constants -/

/-- The round constants are in the scratch space. -/
def Aux (s₀ : State) (m : Mem) : Prop := ∀ j < 24, m.readW (off s₀ (200 + 8 * j)) 64 = RC j

/-- Writes outside the constants keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, 200 ≤ d → d + 8 ≤ 392 → Region.Disjoint ⟨off s₀ d, 8⟩ R) (hf : Frame [R] m m') :
    Aux s₀ m' := fun j hj => by
  rw [hf.readW (Region.contains_self _ _) (by simpa using hR _ (by omega) (by omega)) (by decide)]
  exact h j hj

/-! ## The prologue -/

/-- `movz`, then three `movk`s, build round constant `k`, and the store puts it
in the scratch space. -/
theorem rcStore_ok (k : Nat) (hk : k < 24) (s : State)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (200 + 8 * k)) 8) :
    WP isa (.block (rcStore k)) s fun s' =>
      (∀ r, r ≠ R → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = s.mem.writeW (s.gpr .x1 + BitVec.ofNat 64 (200 + 8 * k)) (RC k) := by
  have _ := hk
  unfold rcStore
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl
    (WP.cons (exec_str_x ⟨by omega, by omega⟩ ?_) (wp_nil ⟨?_, rfl, rfl, rfl, ?_⟩)))))
  · simpa [State.write, R] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true,
      show Reg.x1 ≠ R from by decide, ite_false]
    exact congrArg _ (movz_movk64' _)

/-- During the stores of the round constants. -/
def RcInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .x0 = st s₀ ∧ s.gpr .x1 = scr s₀ ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
    Frame [⟨off s₀ 200, 192⟩] s₀.mem s.mem ∧
    ∀ j < k, s.mem.readW (off s₀ (200 + 8 * j)) 64 = RC j

theorem rcs_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ((List.range 24).flatMap rcStore)) s₀ (RcInv s₀ 24) := by
  refine wp_range_flatMap (M := isa) (RcInv s₀) (fun k s hk ⟨hx0, hx1, hrd, hwr, hsp, hf, hv⟩ => ?_)
    24 le_rfl s₀ ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.mono (rcStore_ok k hk s
    (by rw [hwr, hx1]; exact hp.off_in (by omega))) fun s' ⟨g', r', w', p', m'⟩ => ?_
  rw [hx1] at m'
  refine ⟨by rw [g' _ (by decide), hx0], by rw [g' _ (by decide), hx1], r'.trans hrd, w'.trans hwr,
    p'.trans hsp, ?_, fun j hj => ?_⟩
  · rw [m']
    refine hf.writeW (List.mem_singleton_self _) _ ?_
    have e : scr s₀ + BitVec.ofNat 64 (200 + 8 * k) = off s₀ 200 + BitVec.ofNat 64 (8 * k) := by
      simp only [off]; rw [BitVec.ofNat_add]; ac_rfl
    rw [e]; exact contains_offset (by omega) (by omega)
  · rw [m']
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (scr s₀) (a := 200 + 8 * j) (n := 8) (b := 200 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The rounds' invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = cur s₀ r
  x1 : s.gpr .x1 = oth s₀ r
  x2 : s.gpr .x2 = off s₀ (200 + 8 * r)
  x3 : s.gpr .x3 = off s₀ 392
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : Lanes s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  unfold prologue
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp) fun s₁ ⟨di₁, si₁, rd₁, wr₁, sp₁, f₁, v₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ => wp_addImm (by decide) fun s₃ h₃ => wp_nil ?_
  have m : s₃.mem = s₁.mem := by rw [h₃.mem, h₂.mem]
  have hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₁.mem :=
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, sub_offset (by omega) (by omega)⟩
  refine ⟨by rw [h₃.other _ (by decide), h₂.other _ (by decide), di₁]; simp [cur],
    by rw [h₃.other _ (by decide), h₂.other _ (by decide), si₁]; simp [oth], ?_, ?_,
    by rw [h₃.sp, h₂.sp, sp₁], by rw [h₃.rd, h₂.rd, rd₁], by rw [h₃.wr, h₂.wr, wr₁], ?_,
    fun j hj => by rw [m]; exact v₁ j hj, by rw [m]; exact hf₂⟩
  · rw [h₃.other _ (by decide), h₂.gpr, si₁]
  · rw [h₃.gpr, h₂.other _ (by decide), si₁]
  · intro i hi
    have hc : cur s₀ 0 = st s₀ := by simp [cur]
    rw [hc, m, f₁.readW (lane_contains _ hi)
      (by simpa using hp.region_off (.inl rfl) (d := 200) (n := 192) (by omega) (by omega)) (by decide)]
    simp [Spec.Sha3.stateAt, laneAddr]

/-! ## The rounds -/

theorem off_add8 (s₀ : State) (d : Nat) : off s₀ d + BitVec.ofNat 64 8 = off s₀ (d + 8) := by
  simp only [off]; rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem off_ne0 (s₀ : State) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (off s₀ a - off s₀ b != 0) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    intro e
    apply h
    simp only [off] at e
    bv_omega

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {s : State} (hL : LInv s₀ r s) :
    WP isa (.block round) s fun s' =>
      eval (.nonzero .x T) s' = some (!decide (r + 1 = 24)) ∧ LInv s₀ (r + 1) s' := by
  have he := hp.env r hr
  have hc := cur_cases s₀ r
  have hoth : oth s₀ r = st s₀ ∨ oth s₀ r = scr s₀ := hc.symm.imp (·.2) (·.2)
  refine WP.mono (round_ok s _ _ _ _ (RC r) (by rw [hL.rd, hL.wr]; exact he) hL.x0 hL.x1 hL.x2
    hL.state (hL.aux r hr)) fun s' ⟨hl, hf, hrd, hwr, hsp, h0, h1, h2, h3, hT⟩ => ?_
  have hL' : LInv s₀ (r + 1) s' := by
    refine ⟨by rw [h0, cur_succ], by rw [h1, oth_succ], by rw [h2, off_add8]; congr 1,
      by rw [h3, hL.x3], by rw [hsp, hL.sp], hrd.trans hL.rd, hwr.trans hL.wr, ?_, ?_, ?_⟩
    · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
    · exact hL.aux.frame (fun d hd hd' => (hp.region_off hoth hd (by omega)).symm) hf
    · refine hL.frame.trans (hf.sub fun R hR => ?_)
      simp only [List.mem_singleton] at hR; subst hR
      rcases hoth with e | e <;> rw [e]
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by omega)⟩
  refine ⟨?_, hL'⟩
  rw [eval_nonzero, hT, hL.x3, off_add8, off_ne0 s₀ (by omega) (by omega)]
  simp only [show (200 + 8 * r + 8 = 392) = (r + 1 = 24) by apply propext; omega]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' => s'.sp = s₀.sp ∧ Proof.Sha3.permuteAArch64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  let Inv : Nat → State → Prop := fun n s => ∃ r, n = 24 - r ∧ r < 24 ∧ LInv s₀ r s
  refine WP.loop (M := isa) Inv (fun n s ⟨r, hn, hr, hL⟩ => ?_) 24 s₁ ⟨0, rfl, by omega, h₁⟩
  refine WP.mono (round_step hp hr hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : r + 1 = 24
  · refine .inl ⟨by show VG.AArch64.eval (.nonzero .x T) s' = _; rw [he, hlast]; rfl, by rw [hl.sp], ?_⟩
    show stateAt s'.mem (st s₀) = keccakF (A₀ s₀)
    apply Vector.ext
    intro i hi
    have := hl.state i hi
    simp only [cur, hlast, show 24 % 2 = 0 from rfl, ite_true] at this
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn]
    exact this
  · exact .inr ⟨by show VG.AArch64.eval (.nonzero .x T) s' = _; rw [he]; simp [hlast], 24 - (r + 1), by omega, r + 1, rfl,
      by omega, hl⟩

/-- No instruction writes a callee-saved register. -/
theorem permute_preserved : ∀ r ∈ preserved, ∀ i ∈ instrs permute, dstOf i ≠ some r := by
  have : ((instrs permute).all fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

theorem permute_noCalls : permute.noCalls = true := by decide +kernel

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_verified :
    Verified AArch64.target Impl.Sha3.AArch64.permute Proof.Sha3.permuteAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, hsp, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (permute_preserved r hr) he (.inl permute_noCalls), hsp⟩, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_⟩
    intro a h₁ h₂
    simp only [Region.Contains, satState] at h₁ h₂
    bv_omega

end VG.Proof.Sha3.AArch64
