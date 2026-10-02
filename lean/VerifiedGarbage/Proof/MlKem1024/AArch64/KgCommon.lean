import VerifiedGarbage.Proof.MlKem1024.AArch64.Args
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen

/-!
# ML-KEM-1024 on AArch64: what the proof of `vg_mlkem1024_keygen` shares

The per-target contract, the arguments as buffers (`kA`, `kL`: 0 `seed`, 1
`ek`, 2 `dk`, 3 `scratch`), and what holds from the prologue to the epilogue
(`KB`): the pointers in `x25`–`x28`, our caller's registers saved in
`scratch`, the other callee-saved registers, and the seed. The proof is
ML-KEM-768's (`Proof/MlKem/AArch64/Kg*.lean`, `KeyGen.lean`) for `k = 4` and
ML-KEM-1024's sizes and offsets.
-/

namespace VG.Proof.MlKem1024

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `keyGen(seed = x0, ek = x1, dk = x2, scratch = x3) ->
w0`. -/
def keyGen1024AArch64 : Contract AArch64.isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 64⟩
    let ek : Region := ⟨s.gpr .x1, 1568⟩
    let dk : Region := ⟨s.gpr .x2, 3168⟩
    let scratch : Region := ⟨s.gpr .x3, 49152⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [ek, dk, scratch] ∧ seed.Disjoint ek ∧ seed.Disjoint dk ∧
    seed.Disjoint scratch ∧ ek.Disjoint dk ∧ ek.Disjoint scratch ∧ dk.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint ek ∧ stack.Disjoint dk ∧
    stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => keyGenInternal mlKem1024 iters (bytesAt s.mem (s.gpr .x0) 32)
        (bytesAt s.mem (s.gpr .x0 + 32) 32)) ((s'.gpr .x0).setWidth 32)
      (bytesAt s'.mem (s.gpr .x1) 1568, bytesAt s'.mem (s.gpr .x2) 3168)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
      leakRho (keyGenRho mlKem1024 (bytesAt s₁.mem (s₁.gpr .x0) 32)) =
        leakRho (keyGenRho mlKem1024 (bytesAt s₂.mem (s₂.gpr .x0) 32))

end VG.Proof.MlKem1024

namespace VG.Proof.MlKem1024.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KG VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash copy32)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- The arguments: 0 `seed`, 1 `ek`, 2 `dk`, 3 `scratch`. -/
def kA (s₀ : State) : Nat → Addr
  | 0 => s₀.gpr .x0
  | 1 => s₀.gpr .x1
  | 2 => s₀.gpr .x2
  | _ => s₀.gpr .x3

/-- Their lengths. -/
def kL : Nat → Nat
  | 0 => 64
  | 1 => 1568
  | 2 => 3168
  | _ => 49152

/-- The register we keep each in. -/
def breg : Nat → Reg
  | 0 => .x25
  | 1 => .x26
  | 2 => .x27
  | _ => .x28

theorem kL0 : kL 0 = 64 := rfl
theorem kL1 : kL 1 = 1568 := rfl
theorem kL2 : kL 2 = 3168 := rfl
theorem kL3 : kL 3 = 49152 := rfl

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kA s₀ 0, kL 0⟩]
  wr : s₀.wr = [⟨kA s₀ 1, kL 1⟩, ⟨kA s₀ 2, kL 2⟩, ⟨kA s₀ 3, kL 3⟩]
  args : Args (kA s₀) kL 4 s₀.sp
  sp16 : 16 ≤ s₀.sp.toNat

theorem pre_of {s₀ : State} (h : keyGen1024AArch64.pre s₀) : Pre s₀ := by
  obtain ⟨rd, wr, d01, d02, d03, d12, d13, d23, sp16, k0, k1, k2, k3⟩ := h
  refine ⟨rd, wr, ⟨fun b hb c hc hbc => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | assumption | exact e ‹_›
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> decide
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> assumption

/-! ## What holds throughout -/

/-- Our caller's `x24`–`x28` and `x30`, saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * k)) 64 =
    s₀.gpr ([Reg.x24, .x25, .x26, .x27, .x28, .x30].getD k .x0)

/-- The registers the function keeps for itself. -/
abbrev own : List Reg := [.x24, .x25, .x26, .x27, .x28, .x30]

/-- From the prologue on. -/
structure KB (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x25 : s.gpr .x25 = kA s₀ 0
  x26 : s.gpr .x26 = kA s₀ 1
  x27 : s.gpr .x27 = kA s₀ 2
  x28 : s.gpr .x28 = kA s₀ 3
  cs : ∀ r ∈ preserved, r ∉ own → s.gpr r = s₀.gpr r
  sv : Saved s₀ s.mem
  seed : bytesAt s.mem (kA s₀ 0 + BitVec.ofNat 64 0) 64 = bytesAt s₀.mem (kA s₀ 0 + BitVec.ofNat 64 0) 64
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem KB.breg {s₀ s : State} (h : KB s₀ s) : ∀ {b : Nat}, b < 4 → s.gpr (breg b) = kA s₀ b
  | 0, _ => h.x25
  | 1, _ => h.x26
  | 2, _ => h.x27
  | 3, _ => h.x28

/-- The saved registers are bytes `[SV, SV + 48)` of `scratch`. -/
abbrev svR (s₀ : State) : Region := R (kA s₀) 3 SV 48

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (svR s₀).Disjoint r) : Saved s₀ m' := fun k hk => by
  rw [← h k hk]
  refine hf.readW (r := svR s₀) ?_ hd (by decide)
  rw [show kA s₀ 3 + BitVec.ofNat 64 (SV + 8 * k) = kA s₀ 3 + BitVec.ofNat 64 SV + BitVec.ofNat 64 (8 * k)
    by rw [ptr_add]]
  exact contains_off (by omega) (by decide)

/-- The callee-saved registers but `x24` and `x30`. -/
abbrev kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem pres_kept : ∀ r ∈ preserved, r ∉ own → r ∈ kept := by decide

/-- Memory changes only in `rs`, apart from the saved registers and the seed;
the function's own registers are kept. -/
theorem KB.frame {s₀ s s' : State} (h : KB s₀ s) {rs : List Region} {regs : List Reg}
    (hk : Keep regs s s') (hf : Frame rs s.mem s'.mem) (hr : ∀ r ∈ kept, r ∉ regs)
    (hd : ∀ r ∈ rs, (svR s₀).Disjoint r ∧ (R (kA s₀) 0 0 64).Disjoint r) : KB s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.get .x25 (hr _ (by decide)), h.x25], by rw [hk.get .x26 (hr _ (by decide)), h.x26],
    by rw [hk.get .x27 (hr _ (by decide)), h.x27], by rw [hk.get .x28 (hr _ (by decide)), h.x28],
    fun r hp ho => by rw [hk.get r (hr r (pres_kept r hp ho)), h.cs r hp ho],
    h.sv.frame hf fun r hr => (hd r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hd r hr).2) (by decide), h.seed], fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

theorem KB.block {s₀ s s' : State} (h : KB s₀ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ kept, r ∉ regs) : KB s₀ s' :=
  h.frame (rs := []) hk (by rw [hm]; exact Frame.refl _ _) hr (fun _ h => by cases h)

/-- A call, which changes only memory in `rs` and registers that are not
callee-saved. -/
theorem KB.call {s₀ s s' : State} (h : KB s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hd : ∀ r ∈ rs, (svR s₀).Disjoint r ∧ (R (kA s₀) 0 0 64).Disjoint r) : KB s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.cs _ (by decide) (by decide), h.x25], by rw [hk.cs _ (by decide) (by decide), h.x26],
    by rw [hk.cs _ (by decide) (by decide), h.x27], by rw [hk.cs _ (by decide) (by decide), h.x28],
    fun r hp ho => by
      rw [hk.cs r hp (fun e => ho (by rw [e]; decide)), h.cs r hp ho],
    h.sv.frame hk.frame fun r hr => (hd r hr).1,
    by rw [bytesAt_frame hk.frame (fun r hr => (hd r hr).2) (by decide), h.seed], fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

/-! ## Regions -/

theorem sv_disj {s₀ : State} (hp : Pre s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b)
    (hs : b ≠ 3 ∨ SV + 48 ≤ o ∨ o + l ≤ SV) : (svR s₀).Disjoint (R (kA s₀) b o l) :=
  hp.args.rdisj (by decide) hb (by decide) f (by simp only [SV] at hs ⊢; omega)

theorem seed_disj {s₀ : State} (hp : Pre s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b)
    (hs : b ≠ 0) : (R (kA s₀) 0 0 64).Disjoint (R (kA s₀) b o l) :=
  hp.args.rdisj (by decide) hb (by decide) f (.inl (Ne.symm hs))

/-- Both, as `KB.call` needs them. -/
theorem kb_disj {s₀ : State} (hp : Pre s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b)
    (hs : b ≠ 3 ∨ SV + 48 ≤ o ∨ o + l ≤ SV) (h0 : b ≠ 0) :
    (svR s₀).Disjoint (R (kA s₀) b o l) ∧ (R (kA s₀) 0 0 64).Disjoint (R (kA s₀) b o l) :=
  ⟨sv_disj hp hb f hs, seed_disj hp hb f h0⟩

/-- `kA s₀ b` as a region's base, for the regions the callees are given. -/
theorem stk_R {s₀ s : State} (hp : Pre s₀) (h : KB s₀ s) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b) :
    (stk s).Disjoint (R (kA s₀) b o l) := by
  rw [stk_sp h.sp]; exact hp.args.rstk hb f

theorem below_R {s₀ : State} (hp : Pre s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b) :
    (R (kA s₀) b o l).Disjoint (below s₀.sp 16) := by
  rw [below16]; exact (hp.args.rstk hb f).symm

theorem kb_below {s₀ : State} (hp : Pre s₀) :
    (svR s₀).Disjoint (below s₀.sp 16) ∧ (R (kA s₀) 0 0 64).Disjoint (below s₀.sp 16) :=
  ⟨below_R hp (by decide) (by decide), below_R hp (by decide) (by decide)⟩

/-- Regions a callee may write: in `ek`, `dk` or `scratch`. -/
theorem cov_w {s₀ s : State} (hp : Pre s₀) (h : KB s₀ s) {b o l : Nat} (hb : 1 ≤ b ∧ b < 4)
    (f : o + l ≤ kL b) : Covers [R (kA s₀) b o l] s.wr := by
  rw [h.wr, hp.wr]
  refine R.cov ?_ f
  rcases (by omega : b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl <;> simp

theorem cov_r {s₀ s : State} (hp : Pre s₀) (h : KB s₀ s) {b o l : Nat} (hb : b < 4)
    (f : o + l ≤ kL b) : Covers [R (kA s₀) b o l] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  refine R.cov ?_ f
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> simp

theorem hsetup {s₀ s : State} (hp : Pre s₀) (h : KB s₀ s) {rate : Nat} (hr : rate ∈ Spec.Sha3.rates) :
    HSetup .x28 ST WK rate s := by
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) 3 o l := fun o l => by
    rw [h.x28]
  refine ⟨by decide, by decide, by decide, hr, ?_, by rw [h.sp]; exact hp.sp16, ?_, ?_, ?_⟩
  · rw [e, e]; exact hp.args.rdisj (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [e]; exact stk_R hp h (by decide) (by decide)
  · rw [e]; exact stk_R hp h (by decide) (by decide)
  · rw [e, e]; exact covers_cons (cov_w hp h (by decide) (by decide)) (cov_w hp h (by decide) (by decide))

/-- A piece at bytes `[o, o + l)` of argument `b`, apart from the Keccak
state and working space. -/
theorem pieceOk {s₀ s : State} (hp : Pre s₀) (h : KB s₀ s) {w : Bool} {b o l : Nat} (hb : b < 4)
    (f : o + l ≤ kL b) (hs : b ≠ 3 ∨ 840 ≤ o) (hl : l < 65536) (hw : w = true → 1 ≤ b) :
    PieceOk .x28 ST WK s w ⟨breg b, o, l⟩ := by
  have eb : preg s ⟨breg b, o, l⟩ = R (kA s₀) b o l := by simp only [preg, h.breg hb]
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) 3 o l := fun o l => by
    rw [h.x28]
  have ho : o < 65536 := by
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> simp only [kL] at f <;> omega
  refine ⟨?_, ho, hl, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> decide
  · rw [eb, VG.Proof.MlKem.AArch64.STr, e]
    exact hp.args.rdisj hb (by decide) f (by decide) (by simp only [KG.ST]; omega)
  · rw [eb, VG.Proof.MlKem.AArch64.WKr, e]
    exact hp.args.rdisj hb (by decide) f (by decide) (by simp only [KG.WK]; omega)
  · rw [eb]; exact stk_R hp h hb f
  · rw [eb]
    cases w
    · exact cov_r hp h hb f
    · exact cov_w hp h ⟨hw rfl, hb⟩ f

end VG.Proof.MlKem1024.AArch64.KeyGen
