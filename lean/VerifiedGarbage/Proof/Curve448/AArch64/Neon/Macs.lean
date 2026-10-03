import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Convert

/-!
# The products of a half

Untrusted: everything here is checked by Lean. Running a half's products
leaves, in lane `e` of each target register, its starting value (zero for a
register the half starts) plus the products of the half aimed at it, modulo
2⁶⁴.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside)

/-- The words of a product: `0` and `1`, or `2` and `3` for the `2` forms. -/
abbrev hp (hi : Bool) : Nat := if hi then 2 else 0

/-- Lane `e` of a product of `a` vector `A p.i` and `b` vector `B p.bv`. -/
def prodVal (A B : Nat → BitVec 128) (p : Prod) (e : Nat) : Nat :=
  (vword (A p.i) (hp p.hi + e)).toNat * (vword (B p.bv) (hp p.hi + e)).toNat

/-- The products of `ps` aimed at register `r`, in lane `e`. -/
def prodSum (A B : Nat → BitVec 128) (tgt : Nat → Nat) (ps : List Prod) (r e : Nat) : Int :=
  ((ps.filter fun p => tgt p.pos == r).map fun p => (prodVal A B p e : Int)).sum

theorem prodSum_nil (A B : Nat → BitVec 128) (tgt : Nat → Nat) (r e : Nat) : prodSum A B tgt [] r e = 0 := rfl

theorem prodSum_append (A B : Nat → BitVec 128) (tgt : Nat → Nat) (ps qs : List Prod) (r e : Nat) :
    prodSum A B tgt (ps ++ qs) r e = prodSum A B tgt ps r e + prodSum A B tgt qs r e := by
  simp [prodSum, List.filter_append]

theorem prodSum_single (A B : Nat → BitVec 128) (tgt : Nat → Nat) (p : Prod) (r e : Nat) :
    prodSum A B tgt [p] r e = if tgt p.pos = r then (prodVal A B p e : Int) else 0 := by
  by_cases h : tgt p.pos = r <;> simp [prodSum, h]

/-- Lane `e` of a register, as an integer. -/
abbrev lane (x : BitVec 128) (e : Nat) : Int := ((vdword x e).toNat : Int)

/-- The vector registers a half's products may write. -/
def written (tgt : Nat → Nat) (ps : List Prod) : List Nat := 27 :: ps.map fun p => tgt p.pos


theorem vdword_ofVDwords (a b : BitVec 64) {e : Nat} (he : e < 2) :
    vdword (ofVDwords a b) e = if e = 0 then a else b := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · rw [vdword_ofVDwords_0]; rfl
  · rw [vdword_ofVDwords_1]; rfl

abbrev M64 : Int := 2 ^ 64

theorem lane_lt (x : BitVec 128) (e : Nat) : lane x e < M64 := by
  have := (vdword x e).isLt; simp only [lane, M64]; omega

theorem lane_nonneg (x : BitVec 128) (e : Nat) : 0 ≤ lane x e := Int.natCast_nonneg _

/-- One product: `umull` the first time a register it starts is aimed at, `umlal` after. -/
theorem mac_lane (t : State) (tgt : Nat → Nat) (fresh seen : List Nat) (p : Prod) :
    ∃ x, isa.exec (mac tgt fresh seen p) t = some (t.setV (V (tgt p.pos)) x) ∧ ∀ e < 2,
      lane x e % M64 = ((if tgt p.pos ∈ fresh ∧ tgt p.pos ∉ seen then 0 else lane (t.v (V (tgt p.pos))) e) +
        (vword (t.v (V (23 + p.i))) (hp p.hi + e)).toNat * (vword (t.v (V 27)) (hp p.hi + e)).toNat) % M64 := by
  by_cases hc : tgt p.pos ∈ fresh ∧ tgt p.pos ∉ seen
  · have hm : mac tgt fresh seen p = vo (.umull p.hi (V (tgt p.pos)) (V (23 + p.i)) (V 27)) := by
      simp only [mac, hc, not_false_eq_true, and_self, ite_true]
    rw [hm]
    refine ⟨_, exec_vo_of rfl, fun e he => ?_⟩
    simp only [lane, vdword_ofVDwords _ _ he, hc, not_false_eq_true, and_self, ite_true, Int.zero_add]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
      simp only [ite_true, show (1 : Nat) ≠ 0 by decide, ite_false, umull_lane, Int.natCast_mul]
  · have hm : mac tgt fresh seen p = vo (.umlal p.hi (V (tgt p.pos)) (V (23 + p.i)) (V 27)) := by
      simp only [mac, hc, ite_false]
    rw [hm]
    refine ⟨_, exec_vo_of rfl, fun e he => ?_⟩
    simp only [lane, vdword_ofVDwords _ _ he, hc, ite_false]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
      simp only [ite_true, show (1 : Nat) ≠ 0 by decide, ite_false, umlal_lane] <;>
      rw [Int.natCast_emod, Int.natCast_add, Int.natCast_mul, Int.natCast_pow] <;>
      exact Int.emod_emod_of_dvd _ (Int.dvd_refl _)


/-- The invariant of a half's products, after `done`. -/
structure MInv (s : State) (A B : Nat → BitVec 128) (tgt : Nat → Nat) (fresh : List Nat)
    (done : List Prod) (seen : List Nat) (cur : Option Nat) (t : State) : Prop where
  mem : t.mem = s.mem
  gpr : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  a : ∀ i < 4, t.v (V (23 + i)) = A i
  b : ∀ bv, cur = some bv → t.v (V 27) = B bv
  seenIff : ∀ r, r ∈ seen ↔ ∃ p ∈ done, tgt p.pos = r
  acc : ∀ r < 23, (r ∉ fresh ∨ r ∈ seen) → ∀ e < 2,
    lane (t.v (V r)) e % M64 = ((if r ∈ fresh then 0 else lane (s.v (V r)) e) + prodSum A B tgt done r e) % M64
  other : ∀ r : VReg, (∀ n ∈ written tgt done, r ≠ V n) → t.v r = s.v r

theorem prodSum_unseen {A B : Nat → BitVec 128} {tgt : Nat → Nat} {done : List Prod} {r : Nat}
    (h : ¬ ∃ p ∈ done, tgt p.pos = r) (e : Nat) : prodSum A B tgt done r e = 0 := by
  simp only [prodSum]
  rw [List.filter_eq_nil_iff.mpr fun p hp => by simpa using fun e' => h ⟨p, hp, e'⟩]
  rfl

theorem mod_add_mod (a b : Int) : (a % M64 + b) % M64 = (a + b) % M64 := Int.emod_add_emod _ _ _

/-- The products `ps`, with the `b` vector reloaded when it changes. -/
theorem withLoads_ok {s : State} {base : Addr} (hs : Scr s base) (h : Nat) (tgt : Nat → Nat) (fresh : List Nat)
    (A B : Nat → BitVec 128) (hB : ∀ bv < 9, B bv = s.mem.read (off base (bOff h bv)) 16)
    (hoff : ∀ bv < 9, bOff h bv % 16 = 0 ∧ bOff h bv + 16 ≤ 8192) :
    ∀ (ps done : List Prod) (seen : List Nat) (cur : Option Nat) (t : State),
      (∀ p ∈ ps, p.i < 4 ∧ p.bv < 9 ∧ tgt p.pos < 23) →
      MInv s A B tgt fresh done seen cur t →
      WP isa (.block (withLoads h tgt fresh ps seen cur)) t fun u =>
        ∃ seen' cur', MInv s A B tgt fresh (done ++ ps) seen' cur' u := by
  intro ps
  induction ps with
  | nil => intro done seen cur t _ hi; exact WP.block_nil ⟨seen, cur, by simpa using hi⟩
  | cons p ps ih =>
    intro done seen cur t hps hi
    obtain ⟨pi, pb, pt⟩ := hps p List.mem_cons_self
    have hps' : ∀ q ∈ ps, q.i < 4 ∧ q.bv < 9 ∧ tgt q.pos < 23 := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    simp only [withLoads]
    rw [WP.block_append_iff]
    -- load the `b` vector if it changed
    have load : WP isa (.block (if cur = some p.bv then [] else [ldq 27 (bOff h p.bv)])) t fun t1 =>
        MInv s A B tgt fresh done seen (some p.bv) t1 := by
      split
      · rename_i hc
        exact WP.block_nil { hi with b := fun bv e => hi.b bv (hc ▸ e) }
      · refine WP.block_cons_iff.mpr ⟨_, exec_ldq (scr_of hs hi.gpr hi.wr) 27 (hoff _ pb).1 (hoff _ pb).2, ?_⟩
        refine WP.block_nil ?_
        exact {
          mem := hi.mem, gpr := hi.gpr, rd := hi.rd, wr := hi.wr,
          a := fun i hi' => by
            rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]; exact hi.a i hi'
          b := fun bv e => by
            simp only [Option.some.injEq] at e; subst e
            rw [RegUpd.v_setV_self, hi.mem, hB _ pb]
          seenIff := hi.seenIff,
          acc := fun r hr hrs e he => by
            rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]; exact hi.acc r hr hrs e he
          other := fun r hr => by
            rw [RegUpd.v_setV_of_ne _ _ (hr 27 (by simp [written]))]; exact hi.other r hr }
    refine WP.mono load fun t1 h1 => ?_
    -- the product
    obtain ⟨x, hx, lx⟩ := mac_lane t1 tgt fresh seen p
    refine WP.block_cons_iff.mpr ⟨_, hx, ?_⟩
    have d23 : ∀ i < 4, V (tgt p.pos) ≠ V (23 + i) := fun i hi' => V_ne _ (by omega) _ (by omega) (by omega)
    have d27 : V (tgt p.pos) ≠ V 27 := V_ne _ (by omega) _ (by omega) (by omega)
    refine WP.mono (ih (done ++ [p]) (tgt p.pos :: seen) (some p.bv) (t1.setV (V (tgt p.pos)) x) hps' {
      mem := h1.mem, gpr := h1.gpr, rd := h1.rd, wr := h1.wr,
      a := fun i hi' => by rw [RegUpd.v_setV_of_ne _ _ (d23 i hi').symm]; exact h1.a i hi'
      b := fun bv e => by
        simp only [Option.some.injEq] at e; subst e
        rw [RegUpd.v_setV_of_ne _ _ d27.symm]; exact h1.b _ rfl
      seenIff := fun r => by
        simp only [List.mem_cons, h1.seenIff, List.mem_append, List.not_mem_nil, or_false]
        constructor
        · rintro (rfl | ⟨q, hq, e⟩)
          · exact ⟨p, Or.inr rfl, rfl⟩
          · exact ⟨q, Or.inl hq, e⟩
        · rintro ⟨q, hq | rfl, e⟩
          · exact Or.inr ⟨q, hq, e⟩
          · exact Or.inl e.symm
      acc := fun r hr hrs e he => by
        rw [prodSum_append, prodSum_single]
        by_cases hrd : r = tgt p.pos
        · subst hrd
          rw [RegUpd.v_setV_self, lx e he, ite_eq_left rfl]
          have pv : ((vword (t1.v (V (23 + p.i))) (hp p.hi + e)).toNat : Int) *
              ((vword (t1.v (V 27)) (hp p.hi + e)).toNat : Int) = (prodVal A B p e : Int) := by
            rw [h1.a _ pi, h1.b _ rfl, prodVal]; push_cast; rfl
          rw [pv]
          by_cases hf : tgt p.pos ∈ fresh ∧ tgt p.pos ∉ seen
          · rw [ite_eq_left hf, ite_eq_left hf.1,
              prodSum_unseen (fun hq => hf.2 ((h1.seenIff _).mpr hq))]
            simp
          · rw [ite_eq_right hf]
            have hc : tgt p.pos ∉ fresh ∨ tgt p.pos ∈ seen := by
              by_cases h' : tgt p.pos ∈ fresh
              · exact Or.inr (by by_contra h''; exact hf ⟨h', h''⟩)
              · exact Or.inl h'
            rw [← mod_add_mod, h1.acc _ hr hc e he, mod_add_mod, Int.add_assoc]
        · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) hrd),
            ite_eq_right (Ne.symm hrd), Int.add_zero]
          refine h1.acc r hr ?_ e he
          rcases hrs with h' | h'
          · exact Or.inl h'
          · exact Or.inr ((List.mem_cons.mp h').resolve_left hrd)
      other := fun r hr => by
        rw [RegUpd.v_setV_of_ne _ _ (hr (tgt p.pos) (by simp [written]))]
        exact h1.other r fun n hn => hr n (by
          simp only [written, List.mem_cons, List.map_append, List.mem_append, List.mem_map] at hn ⊢
          rcases hn with hn | ⟨q, hq, e⟩
          · exact Or.inl hn
          · exact Or.inr (Or.inl ⟨q, hq, e⟩)) }) fun u ⟨seen', cur', hu⟩ =>
      ⟨seen', cur', by simpa only [List.append_assoc, List.singleton_append] using hu⟩


theorem prods_facts : ∀ p ∈ prods, p.i < 4 ∧ p.bv < 9 := by decide

/-- A half product: the `a` vectors, then the products. -/
theorem half_ok {s : State} {base : Addr} (hs : Scr s base) {h : Nat} (tgt : Nat → Nat) (fresh : List Nat)
    (ht : ∀ p ∈ prods, tgt p.pos < 23)
    (ha : ∀ i < 4, (aHalf h + 16 * i) % 16 = 0 ∧ aHalf h + 16 * i + 16 ≤ 8192)
    (hoff : ∀ bv < 9, bOff h bv % 16 = 0 ∧ bOff h bv + 16 ≤ 8192) :
    WP isa (.block (half h tgt fresh)) s fun u =>
      u.mem = s.mem ∧ u.gpr = s.gpr ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      (∀ r < 23, (r ∉ fresh ∨ ∃ p ∈ prods, tgt p.pos = r) → ∀ e < 2,
        lane (u.v (V r)) e % M64 = ((if r ∈ fresh then 0 else lane (s.v (V r)) e) +
          prodSum (fun i => s.mem.read (off base (aHalf h + 16 * i)) 16)
            (fun bv => s.mem.read (off base (bOff h bv)) 16) tgt prods r e) % M64) ∧
      (∀ r : VReg, (∀ n ∈ [23, 24, 25, 26, 27], r ≠ V n) → (∀ p ∈ prods, r ≠ V (tgt p.pos)) → u.v r = s.v r) := by
  simp only [half, List.map, List.range, List.range.loop, List.cons_append, List.nil_append]
  let A := fun i => s.mem.read (off base (aHalf h + 16 * i)) 16
  let B := fun bv => s.mem.read (off base (bOff h bv)) 16
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq hs 23 (ha 0 (by decide)).1 (ha 0 (by decide)).2, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g1 24 (ha 1 (by decide)).1 (ha 1 (by decide)).2, ?_⟩
  case g1 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g2 25 (ha 2 (by decide)).1 (ha 2 (by decide)).2, ?_⟩
  case g2 => scr
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq (base := base) ?g3 26 (ha 3 (by decide)).1 (ha 3 (by decide)).2, ?_⟩
  case g3 => scr
  simp only [RegUpd.mem_setV]
  generalize ht4 : ((((s.setV (V 23) (A 0)).setV (V 24) (A 1)).setV (V 25) (A 2)).setV (V 26) (A 3)) = t4
  have v4 : ∀ r : VReg, (∀ n ∈ [23, 24, 25, 26], r ≠ V n) → t4.v r = s.v r := by
    intro r hr
    rw [← ht4]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
    rw [RegUpd.v_setV_of_ne _ _ hr.2.2.2, RegUpd.v_setV_of_ne _ _ hr.2.2.1, RegUpd.v_setV_of_ne _ _ hr.2.1,
      RegUpd.v_setV_of_ne _ _ hr.1]
  have i0 : MInv t4 A B tgt fresh [] [] none t4 := {
    mem := rfl, gpr := rfl, rd := rfl, wr := rfl,
    a := fun i hi => by
      rw [← ht4]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) only [RegUpd.v_setV, ite_true, ite_false]
    b := fun _ e => by cases e
    seenIff := fun r => by simp
    acc := fun r hr hrs e he => by
      have hf : r ∉ fresh := by simpa using hrs
      simp [prodSum, hf]
    other := fun _ _ => rfl }
  have hB : ∀ bv < 9, B bv = t4.mem.read (off base (bOff h bv)) 16 := fun bv _ => by rw [← ht4]; rfl
  refine WP.mono (withLoads_ok (scr_of hs (by rw [← ht4]; rfl) (by rw [← ht4]; rfl)) h tgt fresh A B hB hoff prods [] [] none t4
    (fun p hp => ⟨(prods_facts p hp).1, (prods_facts p hp).2, ht p hp⟩) i0) fun u ⟨seen, cur, hu⟩ => ?_
  have m4 : t4.mem = s.mem := by rw [← ht4]; rfl
  refine ⟨hu.mem.trans m4, hu.gpr.trans (by rw [← ht4]; rfl), hu.rd.trans (by rw [← ht4]; rfl),
    hu.wr.trans (by rw [← ht4]; rfl), fun r hr hrs e he => ?_, fun r h1 h2 => ?_⟩
  · have hrs' : r ∉ fresh ∨ r ∈ seen := by
      rcases hrs with h' | ⟨p, hp, e'⟩
      · exact Or.inl h'
      · exact Or.inr ((hu.seenIff r).mpr ⟨p, by simpa using hp, e'⟩)
    rw [hu.acc r hr hrs' e he, List.nil_append, v4 _ (fun n hn => V_ne _ (by omega) _ (by simp at hn; omega)
      (by simp at hn; omega))]
  · rw [hu.other r (fun n hn => by
        simp only [written, List.nil_append, List.mem_cons, List.mem_map] at hn
        rcases hn with rfl | ⟨p, hp, rfl⟩
        · exact h1 27 (by simp)
        · exact h2 p hp),
      v4 r (fun n hn => h1 n (by simp at hn ⊢; omega))]

end VG.Proof.Curve448.AArch64.Neon
