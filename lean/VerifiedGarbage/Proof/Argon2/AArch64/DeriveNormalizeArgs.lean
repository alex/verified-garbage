import VerifiedGarbage.Proof.Argon2.AArch64.DeriveNormalize

/-! Normalize distinct stack slots while retaining every other frame word. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def normalizedWord (s : State) (d : Nat) : Addr :=
  (((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)

structure NormalizedArgs (s t : State) (ds : List Nat) : Prop where
  values : ∀ d ∈ ds, t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = normalizedWord s d
  regs : ∀ r, r ≠ .x8 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame (ds.map fun d => (⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩ : Region)) s.mem t.mem

theorem NormalizedArgs.other_word {s t : State} {ds : List Nat} (h : NormalizedArgs s t ds)
    (e : Nat) (bound : e + 8 < 2 ^ 64)
    (separate : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .x19 (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate d hd) (Nat.le_of_lt bound) (Nat.le_of_lt (bounds d hd))

theorem normalizeArgs_ok (ds : List Nat) (s : State)
    (encoding : ∀ d ∈ ds, d % 8 = 0 ∧ d < 32768)
    (read : ∀ d ∈ ds, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ ds, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8)
    (separate : ds.Pairwise fun d e => d + 8 ≤ e ∨ e + 8 ≤ d)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    WP isa (Impl.Argon2.AArch64.Derive.normalizeArgs ds) s (NormalizedArgs s · ds) := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine (normalize_ok s d (encoding d (by simp)).1 (encoding d (by simp)).2 (read d (by simp)) (write d (by simp))).mono ?_
      intro t ht
      exact ⟨fun e he => by simp only [List.mem_singleton] at he; subst e; exact ht.word,
        ht.regs, ht.rd, ht.wr, ht.sp, ht.frame⟩
    | cons e ds =>
      obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
      refine WP.seq ((normalize_ok s d (encoding d (List.mem_cons_self ..)).1
        (encoding d (List.mem_cons_self ..)).2 (read d (List.mem_cons_self ..))
        (write d (List.mem_cons_self ..))).mono ?_)
      intro t ht
      refine (ih t (fun x hx => encoding x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.rd, ht.wr, ht.regs .x19 (by decide)]; exact read x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.wr, ht.regs .x19 (by decide)]; exact write x (List.mem_cons_of_mem d hx))
        tailSep (fun x hx => bounds x (List.mem_cons_of_mem d hx))).mono ?_
      intro u hu
      refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
        hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.sp.trans ht.sp, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hu.other_word x (bounds x (List.mem_cons_self ..)) headSep
            (fun a ha => bounds a (List.mem_cons_of_mem x ha))]
          exact ht.word
        · rw [hu.values x hx]
          unfold normalizedWord
          have sep : x + 8 ≤ d ∨ d + 8 ≤ x := (headSep x hx).symm
          rw [ht.other_word x sep (bounds x (List.mem_cons_of_mem d hx)) (bounds d (List.mem_cons_self ..))]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs .x19 (by decide)] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..

end VG.Proof.Argon2.AArch64.Derive
