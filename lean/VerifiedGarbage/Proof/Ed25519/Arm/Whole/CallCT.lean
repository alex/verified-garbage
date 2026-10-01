import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Framework.Arm.RelCT

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm

structure CallReady (k : Contract isa) (E : BitVec 32) (rd wr : List Region) (t : State) where
  reads : List Region
  writes : List Region
  pre : k.pre (t.callEntry.withRegions reads writes)
  covers : Covers (reads ++ writes) (rd ++ FR E :: wr)
  writable : ∀ r ∈ writes, Within r (FR E) ∨ ∃ R ∈ wr, Within r R

theorem CallReady.covers_state {k : Contract isa} {E : BitVec 32} {g : Reg → BitVec 32}
    {m : Mem} {rd wr : List Region} {t : State} (hc : Ctx E g m rd wr t)
    (h : CallReady k E rd wr t) :
    Covers (h.reads ++ h.writes) (t.rd ++ t.wr) ∧ Covers h.writes t.wr := by
  refine ⟨by rw [hc.rd, hc.wr]; exact h.covers, Covers.of_sub fun r hr => ?_⟩
  rw [hc.wr]
  rcases h.writable r hr with h | ⟨R, hr, h⟩
  · exact ⟨FR E, List.mem_cons_self, h⟩
  · exact ⟨R, List.mem_cons_of_mem _ hr, h⟩

theorem CallReady.wp {k : Contract isa} {E : BitVec 32} {g : Reg → BitVec 32}
    {m : Mem} {rd wr : List Region} {t : State} (hc : Ctx E g m rd wr t)
    (h : CallReady k E rd wr t) {c : Prog isa} {name : String}
    (hv : ∀ s, k.pre s → ∃ trace s', Exec isa c s trace s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noFrames = true) :
    WP isa (.call name c) t (Ctx E g m rd wr) :=
  call_ok hc hv hn h.pre h.covers h.writable fun _ hc _ _ => hc

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

end VG.Proof.Ed25519.Arm.Whole
