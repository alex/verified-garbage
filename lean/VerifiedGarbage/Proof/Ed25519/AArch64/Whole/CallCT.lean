import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout

/-! Merged from `Proof.Ed25519.AArch64.Whole.BlocksCT`. -/
section
/-! Equal traces for straight-line helpers addressed through the public SP. -/
namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

theorem block_rel {P : State → State → Prop} {is : List Instr}
    (he : ∀ a b, P a b → a.sp = b.sp)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (VG.AArch64.Taint.ofRegs []) (.block is) hint).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (VG.AArch64.Taint.ofRegs [])
    (fun a b h => ⟨he a b h, fun r hr => by simp at hr⟩) ht

theorem rel_wp {F F' G G' : State → Prop} {c : Prog isa}
    (hct : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True)
    (ha : ∀ a, F a → WP isa c a G) (hb : ∀ b, F' b → WP isa c b G') :
    RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b :=
  (hct.wp fun a b h => ⟨ha a h.1, hb b h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end VG.Proof.Ed25519.AArch64.Whole
end

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

structure CallReady (k : Contract isa) (E : BitVec 64) (rd wr : List Region) (t : State) where
  reads : List Region
  writes : List Region
  pre : k.pre (t.callEntry.withRegions reads writes)
  covers : Covers (reads ++ writes) (rd ++ FR E :: wr)
  writable : ∀ r ∈ writes, Within r (FR E) ∨ ∃ R ∈ wr, Within r R

theorem CallReady.covers_state {k : Contract isa} {E : BitVec 64} {g : Reg → BitVec 64}
    {v : VReg → BitVec 128} {m : Mem} {rd wr : List Region} {t : State} (hc : Ctx E g v m rd wr t)
    (h : CallReady k E rd wr t) :
    Covers (h.reads ++ h.writes) (t.rd ++ t.wr) ∧ Covers h.writes t.wr := by
  refine ⟨by rw [hc.rd, hc.wr]; exact h.covers, Covers.of_sub fun r hr => ?_⟩
  rw [hc.wr]
  rcases h.writable r hr with h | ⟨R, hr, h⟩
  · exact ⟨FR E, List.mem_cons_self, h⟩
  · exact ⟨R, List.mem_cons_of_mem _ hr, h⟩

theorem CallReady.wp {k : Contract isa} {E : BitVec 64} {g : Reg → BitVec 64}
    {v : VReg → BitVec 128} {m : Mem} {rd wr : List Region} {t : State} (hc : Ctx E g v m rd wr t)
    (h : CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) :
    WP isa (.call name c) t (Ctx E g v m rd wr) :=
  call_ok hc hv hn h.pre h.covers h.writable fun _ hc _ _ => hc

theorem CallReady.wpF {k : Contract isa} {E : BitVec 64} {g : Reg → BitVec 64}
    {v : VReg → BitVec 128} {m : Mem} {rd wr : List Region} {t : State} (hc : Ctx E g v m rd wr t)
    (h : CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : c.aarch64Depth ≤ 1) :
    WP isa (.call name c) t (Ctx E g v m rd wr) :=
  call_okF hc hv hd h.pre h.covers h.writable fun _ hc _ _ => hc

/-- Independent permission narrowing in each run leaves call traces unchanged. -/
theorem callEx {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ a b, P a b → ∃ ar aw br bw,
      k.pre (a.callEntry.withRegions ar aw) ∧ k.pre (b.callEntry.withRegions br bw) ∧
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw) ∧
      Covers (ar ++ aw) (a.rd ++ a.wr) ∧ Covers aw a.wr ∧
      Covers (br ++ bw) (b.rd ++ b.wr) ∧ Covers bw b.wr) :
    RelCT isa P (.call n c) fun _ _ => True := by
  intro a b ta tb a' b' hp ea eb
  obtain ⟨ar, aw, br, bw, pa, pb, pub, ca, wa, cb, wb⟩ := hP a b hp
  cases ea with
  | call ha xa ra =>
    cases eb with
    | call hb xb rb =>
      rw [call_callEntry, Option.some.injEq] at ha hb
      subst ha hb
      obtain ⟨_, na⟩ := trace_narrow hv pa (by simpa using ca) (by simpa using wa) xa
      obtain ⟨_, nb⟩ := trace_narrow hv pb (by simpa using cb) (by simpa using wb) xb
      have ht := hct _ _ _ _ _ _ pa pb pub na nb
      exact ⟨by simp only [ht], trivial⟩

end VG.Proof.Ed25519.AArch64.Whole
