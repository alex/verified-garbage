import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlKem.Arm.HashTop
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ML-DSA on 32-bit ARM: bytes, copies and the sponge in the buffers of a `Site`

A byte stored (`setB_ok`), bytes copied (`copyS`, from ML-KEM's `copy_loop`),
and the sponge (`hashS`, from ML-KEM's `hash_ok`), with what they change as
triples of the layout.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece hash copy copyBody)
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad rates)
open VG.Proof.MlKem.Arm (PieceOk Outs)

/-- The byte `v` moved by `movw` and stored by `strb`. -/
theorem byte16 (v : Nat) : ((BitVec.ofNat 16 v).setWidth 32).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section
variable {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s)
include hs

/-! ## A byte -/

theorem setB_ok {q : Ptr} (pq : PtrIn L q 1) (hw : ix q.1 ∈ Wb) (ho : q.2 < 4096) (v : Nat) :
    WP isa (.block (setB q v)) s fun s' =>
      Kept (L.RL [tri q 1]) s s' ∧ bytesAt s'.mem (lpa L q) 1 = [BitVec.ofNat 8 v] := by
  have gb := hs.val pq.1
  simp only [argVal] at gb
  have ea := hs.addrE pq (by decide)
  have hi : InRegions s.wr (State.addr (s.gpr q.1 + BitVec.ofNat 32 q.2)) 1 := by
    rw [gb, ea]; exact hs.cwE pq hw _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have n12 : q.1 ≠ .r12 := by
    have := pq.1; simp only [argOk, Bool.or_eq_true, beq_iff_eq] at this
    rcases this with ((h | h) | h) | h <;> rw [h] <;> decide
  have n12' : ¬ q.1 = .r12 := n12
  rw [gb, ea] at hi
  run_block [setB, hi, ho, n12', gb, ea]
  refine ⟨⟨fun r hr hl => ?_, rfl, rfl, rfl, ?_⟩, ?_⟩
  · have : r ≠ .r12 := by revert r; decide
    simp only [this, ite_false]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [show ∀ (m : Mem) (a : Addr), bytesAt m a 1 = [m a] from fun _ _ => by simp [bytesAt], VG.WriteBytes.writeW8_apply,
      ite_eq_left rfl, byte16 v]

omit hs in
/-- A register of the layout is callee-saved (and not `lr`). -/
theorem base_pres {r : Reg} (h : argOk (.ptr (r, 0)) = true) : r ∈ preserved ∧ r ≠ .lr := by
  simp only [argOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;> decide

/-! ## A copy -/

theorem copyS {sb db : Reg} {so dO len : Nat} (ps : PtrIn L (sb, so) len) (pd : PtrIn L (db, dO) len)
    (wd : ix db ∈ Wb) (hse : encodable (BitVec.ofNat 32 so) = true) (hde : encodable (BitVec.ofNat 32 dO) = true)
    (hle : encodable (BitVec.ofNat 32 len) = true) (hlen : len < 2 ^ 32) (hl0 : 0 < len)
    (hd : sepB L.sizes (tri (sb, so) len) (tri (db, dO) len) = true) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [tri (db, dO) len]) s s' ∧ bytesAt s'.mem (lpa L (db, dO)) len = bytesAt s.mem (lpa L (sb, so)) len := by
  have gs := hs.val ps.1
  have gd := hs.val pd.1
  simp only [argVal] at gs gd
  obtain ⟨ea, fa⟩ := hs.addr ps.2 hl0
  obtain ⟨eb, fb⟩ := hs.addr pd.2 hl0
  refine WP.seq (WP.mono (copy_setup (base_pres (by simpa [argOk] using ps.1))
    (base_pres (by simpa [argOk] using pd.1)) hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs] at g0; rw [gd] at g1
  have hdj := hs.dE hd (.inr wd)
  refine WP.mono (copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact hdj)
    (by rw [ea, o₁.rd, o₁.wr]; exact hs.crE ps)
    (by rw [eb, o₁.wr]; exact hs.cwE pd wd) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## The sponge -/

omit hs in
theorem ix_ne1 (r : Reg) : ix r ≠ 1 := by cases r <;> decide

theorem hashS {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hre : encodable (BitVec.ofNat 32 rate) = true)
    (hse : encodable (BitVec.ofNat 32 sfx) = true) (hsfx : sfx < 256) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, PieceOk (hashLay L s K) ix s false p) (hq : PieceOk (hashLay L s K) ix s true q) :
    WP isa (hash rate sfx ins [q]) s fun s' =>
      Kept (L.RL [(0, 0, 200), (0, 200, 640), (1, 0, STK), (ix q.base, q.off, q.len)]) s s' ∧
      bytesAt s'.mem (L.A (ix q.base) q.off) q.len = squeezeFrom rate (absorb rate
        (pad rate (BitVec.ofNat 8 sfx) (ins.map ((hashLay L s K).pb ix s.mem)).flatten)) 0 q.len := by
  refine WP.mono (hash_ok hrate hre hse hsfx (hs.ctx hK) hne hin (fun p hp => by
    rw [List.mem_singleton] at hp; subst hp; exact hq) (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ => ⟨?_, ?_⟩
  · refine ⟨k.cs, k.sp, k.rd, k.wr, k.frame.sub fun r hr => ?_⟩
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by
        rw [hashLay_R L s K (by decide)]; exact fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      have := hs.belowSub (n := 8) hs.s8
      intro x hx
      apply this
      have := hs.spk; have := hs.s8
      have := addr_toNat' s.sp
      have := addr_toNat' (s.sp - BitVec.ofNat 32 8)
      simp only [Region.Contains, hashLay, ite_true] at hx ⊢
      bv_omega
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), by
        rw [hashLay_R L s K (ix_ne1 _)]; exact fun _ h => h⟩
  · have := o.1
    simp only [Lay.pb, hashLay_ptr L s K (ix_ne1 _)] at this
    exact this

/-- A piece of the sponge, in a buffer of the layout. -/
theorem pieceS {K : Nat → Bool} {w : Bool} {p : Piece} (hb : argOk (.ptr (p.base, 0)) = true)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll (hashLay L s K).sizes (ix p.base, p.off, p.len) kRegs = true)
    (hK : ix p.base = 0 ∨ K (ix p.base) = true) (hw : w = true → ix p.base ∈ Wb) :
    PieceOk (hashLay L s K) ix s w p := by
  have hi5 : ix p.base < 5 := by
    simp only [argOk, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((h | h) | h) | h <;> rw [h] <;> decide
  have e := hashLay_size L s (ix_ne1 p.base) hK hi5
  refine ⟨base_pres hb, by rw [hashLay_ptr L s K (ix_ne1 _)]; exact hs.base hb, hoe, hle, hpos, hlt, hsep, ?_⟩
  rw [hashLay_ptr L s K (ix_ne1 _), e]
  cases w with
  | true => exact hs.cw _ (hw rfl) (ix_ne1 _)
  | false => exact hs.cr _ hi5 (ix_ne1 _)

end

/-! ## What a part keeps -/

section
variable {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
  (hf : Frame (L.RL W) m m') {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : i ∈ Wb)
include hL hf h hw

omit hf in
theorem keepD : ∀ r ∈ L.RL W, (L.R i o l).Disjoint r := fun r hr => by
  obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
  exact disjW hL (List.all_eq_true.mp h w hw') (.inl hw)

theorem bytes_keepW (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (keepD hL h hw) hl

section
variable (hl : l = 1024)
include hl

theorem polyIs_keepW {f : Spec.MlDsa.Poly} (hp : Spec.MlDsa.PolyIs m (L.A i o) f) : Spec.MlDsa.PolyIs m' (L.A i o) f :=
  Proof.MlDsa.Verify.polyIs_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this) hp

theorem reduced_keepW (hp : Spec.MlDsa.Reduced m (L.A i o)) : Spec.MlDsa.Reduced m' (L.A i o) :=
  Proof.MlDsa.Verify.reduced_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this) hp

theorem polyAt_keepW : Spec.MlDsa.polyAt m' (L.A i o) = Spec.MlDsa.polyAt m (L.A i o) :=
  Proof.MlDsa.Verify.polyAt_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this)

theorem natPolyAt_keepW : Spec.MlDsa.natPolyAt m' (L.A i o) = Spec.MlDsa.natPolyAt m (L.A i o) :=
  Proof.MlDsa.Verify.natPolyAt_frame hf (fun r hr => by have := keepD hL h hw r hr; subst hl; exact this)

end

end

end VG.Proof.MlDsa.Arm.KeyGen
