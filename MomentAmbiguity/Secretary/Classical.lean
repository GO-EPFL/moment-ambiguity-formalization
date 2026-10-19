import MomentAmbiguity.Secretary.ClassicalInterface
import MomentAmbiguity.Secretary.ClassicalLP
import Mathlib.GroupTheory.Perm.Fin

/-!
# The classical finite secretary theorem

This module closes the finite classical interfaces used by the manuscript.  The proof uses
the independent insertion-rank encoding of a permutation and the exact finite secretary LP.
-/

open scoped BigOperators Topology

namespace MomentAmbiguity

open Filter Set
open External

noncomputable section

/-! ## Order-preserving insertion codes -/

/-- Append a last arrival of relative rank `p` to a permutation.  Unlike mathlib's
`Equiv.Perm.decomposeFin`, the unused ranks are relabelled by the order-preserving
`Fin.succAbove`. -/
def secretaryPermSnoc {n : ℕ} (e : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective
    (Fin.lastCases p (fun i ↦ p.succAbove (e i)))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j hij
      by_cases hi : i = Fin.last n
      · subst i
        by_cases hj : j = Fin.last n
        · exact hj.symm
        · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact False.elim (p.succAbove_ne (e j) hij.symm)
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
        by_cases hj : j = Fin.last n
        · subst j
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact False.elim (p.succAbove_ne (e i) hij)
        · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
          simp only [Fin.lastCases_castSucc] at hij
          exact congrArg Fin.castSucc (e.injective
            ((Fin.strictMono_succAbove p).injective hij))
      , rfl⟩)

@[simp]
theorem secretaryPermSnoc_last {n : ℕ} (e : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    secretaryPermSnoc e p (Fin.last n) = p := by
  simp [secretaryPermSnoc]

@[simp]
theorem secretaryPermSnoc_castSucc {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) (i : Fin n) :
    secretaryPermSnoc e p i.castSucc = p.succAbove (e i) := by
  simp [secretaryPermSnoc]

/-- Delete the last arrival, relabelling the remaining ranks in increasing order. -/
def secretaryPermInit {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin n) :=
  let p := e (Fin.last n)
  Equiv.ofBijective
    (fun i ↦ (finSuccAboveEquiv p).symm
      ⟨e i.castSucc, by
        intro h
        have heq : i.castSucc = Fin.last n := e.injective (by simpa [p] using h)
        exact Fin.castSucc_ne_last i heq⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j hij
      have hsub :
          (⟨e i.castSucc, by
            intro h
            exact Fin.castSucc_ne_last i (e.injective (by simpa [p] using h))⟩ :
              {x : Fin (n + 1) // x ≠ p}) =
          ⟨e j.castSucc, by
            intro h
            exact Fin.castSucc_ne_last j (e.injective (by simpa [p] using h))⟩ :=
        (finSuccAboveEquiv p).symm.injective hij
      exact Fin.castSucc_injective _ (e.injective (congrArg Subtype.val hsub))
      , rfl⟩)

@[simp]
theorem secretaryPerm_init_snoc {n : ℕ} (e : Equiv.Perm (Fin (n + 1))) :
    secretaryPermSnoc (secretaryPermInit e) (e (Fin.last n)) = e := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp
  · simp only [secretaryPermSnoc_castSucc]
    change (e (Fin.last n)).succAbove
      ((finSuccAboveEquiv (e (Fin.last n))).symm ⟨e i.castSucc, _⟩) = e i.castSucc
    exact congrArg Subtype.val
      ((finSuccAboveEquiv (e (Fin.last n))).apply_symm_apply ⟨e i.castSucc, _⟩)

/-- Appending an order-preserving last rank is a bijection. -/
def secretaryPermSnocPairEquiv (n : ℕ) :
    Equiv.Perm (Fin n) × Fin (n + 1) ≃ Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun ep ↦ secretaryPermSnoc ep.1 ep.2) ⟨by
    rintro ⟨e, p⟩ ⟨f, q⟩ h
    have hpq : p = q := by
      simpa using congrArg (fun g : Equiv.Perm (Fin (n + 1)) ↦ g (Fin.last n)) h
    subst q
    apply Prod.ext
    · apply Equiv.ext
      intro i
      apply (Fin.strictMono_succAbove p).injective
      simpa using congrArg (fun g : Equiv.Perm (Fin (n + 1)) ↦ g i.castSucc) h
    · rfl
    , by
      intro g
      exact ⟨(secretaryPermInit g, g (Fin.last n)), secretaryPerm_init_snoc g⟩⟩

/-- Order-preserving deletion of the last arrival is an equivalence. -/
def secretaryPermSnocEquiv (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃ Equiv.Perm (Fin n) × Fin (n + 1) :=
  (secretaryPermSnocPairEquiv n).symm

@[simp]
theorem secretaryPermSnocEquiv_snoc {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) :
    secretaryPermSnocEquiv n (secretaryPermSnoc e p) = (e, p) :=
  (secretaryPermSnocPairEquiv n).symm_apply_apply (e, p)

/-- The independent relative rank observed at every arrival. -/
abbrev SecretaryRankCode (m : ℕ) := (t : Fin m) → Fin (t.val + 1)

/-- Append one insertion rank to a rank code. -/
def secretaryRankCodeSnoc {n : ℕ} (c : SecretaryRankCode n) (p : Fin (n + 1)) :
    SecretaryRankCode (n + 1) :=
  Fin.lastCases p (fun i ↦ c i)

@[simp]
theorem secretaryRankCodeSnoc_last {n : ℕ} (c : SecretaryRankCode n)
    (p : Fin (n + 1)) : secretaryRankCodeSnoc c p (Fin.last n) = p := by
  simp [secretaryRankCodeSnoc]

@[simp]
theorem secretaryRankCodeSnoc_castSucc {n : ℕ} (c : SecretaryRankCode n)
    (p : Fin (n + 1)) (i : Fin n) : secretaryRankCodeSnoc c p i.castSucc = c i := by
  simp [secretaryRankCodeSnoc]

/-- Split off the last coordinate of a rank code. -/
def secretaryRankCodeSnocEquiv (n : ℕ) :
    SecretaryRankCode (n + 1) ≃ SecretaryRankCode n × Fin (n + 1) where
  toFun c := (fun i ↦ c i.castSucc, c (Fin.last n))
  invFun cp := secretaryRankCodeSnoc cp.1 cp.2
  left_inv c := by
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [secretaryRankCodeSnoc]
  right_inv cp := by
    rcases cp with ⟨c, p⟩
    apply Prod.ext
    · funext i
      simp [secretaryRankCodeSnoc]
    · simp [secretaryRankCodeSnoc]

@[simp]
theorem secretaryRankCodeSnocEquiv_symm_apply {n : ℕ}
    (c : SecretaryRankCode n) (p : Fin (n + 1)) :
    (secretaryRankCodeSnocEquiv n).symm (c, p) = secretaryRankCodeSnoc c p := rfl

/-- Uniform permutations are equivalent to independent insertion ranks. -/
def secretaryPermRankCodeEquiv : (m : ℕ) →
    Equiv.Perm (Fin m) ≃ SecretaryRankCode m
  | 0 =>
      ⟨fun _ i ↦ Fin.elim0 i,
       fun _ ↦ Equiv.refl _,
       fun e ↦ Subsingleton.elim _ _,
       fun c ↦ funext fun i ↦ Fin.elim0 i⟩
  | n + 1 =>
      (secretaryPermSnocEquiv n).trans
        (((secretaryPermRankCodeEquiv n).prodCongr (Equiv.refl _)).trans
          (secretaryRankCodeSnocEquiv n).symm)

@[simp]
theorem secretaryPermRankCodeEquiv_snoc {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) :
    secretaryPermRankCodeEquiv (n + 1) (secretaryPermSnoc e p) =
      secretaryRankCodeSnoc (secretaryPermRankCodeEquiv n e) p := by
  rw [secretaryPermRankCodeEquiv]
  simp only [Equiv.trans_apply, secretaryPermSnocEquiv_snoc, Equiv.prodCongr_apply]
  change (secretaryRankCodeSnocEquiv n).symm
    (secretaryPermRankCodeEquiv n e, p) = _
  exact secretaryRankCodeSnocEquiv_symm_apply _ _

theorem card_secretaryRankCode (m : ℕ) :
    Fintype.card (SecretaryRankCode m) = m.factorial := by
  rw [← Fintype.card_congr (secretaryPermRankCodeEquiv m)]
  simp [Fintype.card_perm]

/-- Decode an insertion-rank code. -/
def secretaryPermOfRankCode {m : ℕ} (c : SecretaryRankCode m) :
    Equiv.Perm (Fin m) := (secretaryPermRankCodeEquiv m).symm c

@[simp]
theorem secretaryPermOfRankCode_snoc {n : ℕ} (c : SecretaryRankCode n)
    (p : Fin (n + 1)) :
    secretaryPermOfRankCode (secretaryRankCodeSnoc c p) =
      secretaryPermSnoc (secretaryPermOfRankCode c) p := by
  apply (secretaryPermRankCodeEquiv (n + 1)).injective
  simp [secretaryPermOfRankCode]

/-- Equality of all observed insertion ranks through `t`. -/
def SecretaryRankCodeAgreeThrough {m : ℕ} (t : Fin m)
    (c d : SecretaryRankCode m) : Prop :=
  ∀ i : Fin m, i ≤ t → c i = d i

theorem sameRelativePrefix_snoc_castSucc {n : ℕ} (e f : Equiv.Perm (Fin n))
    (p q : Fin (n + 1)) (t : Fin n) :
    SameRelativePrefix t.castSucc (secretaryPermSnoc e p) (secretaryPermSnoc f q) ↔
      SameRelativePrefix t e f := by
  constructor
  · intro h i j hi hj
    have h' := h i.castSucc j.castSucc (by simpa) (by simpa)
    simpa only [secretaryPermSnoc_castSucc, Fin.succAbove_lt_succAbove_iff] using h'
  · intro h i j hi hj
    have hit : i ≠ Fin.last n := by
      intro hit
      subst i
      exact (not_le_of_gt t.castSucc_lt_last) hi
    have hjt : j ≠ Fin.last n := by
      intro hjt
      subst j
      exact (not_le_of_gt t.castSucc_lt_last) hj
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hit
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hjt
    simpa only [secretaryPermSnoc_castSucc, Fin.succAbove_lt_succAbove_iff] using
      h i j (by simpa using hi) (by simpa using hj)

theorem rankCodeAgreeThrough_snoc_castSucc {n : ℕ}
    (c d : SecretaryRankCode n) (p q : Fin (n + 1)) (t : Fin n) :
    SecretaryRankCodeAgreeThrough t.castSucc
        (secretaryRankCodeSnoc c p) (secretaryRankCodeSnoc d q) ↔
      SecretaryRankCodeAgreeThrough t c d := by
  constructor
  · intro h i hi
    simpa using h i.castSucc (by simpa)
  · intro h i hi
    have hit : i ≠ Fin.last n := by
      intro hit
      subst i
      exact (not_le_of_gt t.castSucc_lt_last) hi
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hit
    simpa using h i (by simpa using hi)

/-- Insertion-code prefix equality implies equality of every observed relative comparison. -/
theorem rankCodeAgreeThrough_sameRelativePrefix : ∀ {m : ℕ} (t : Fin m)
    (c d : SecretaryRankCode m), SecretaryRankCodeAgreeThrough t c d →
      SameRelativePrefix t (secretaryPermOfRankCode c) (secretaryPermOfRankCode d)
  | 0, t => Fin.elim0 t
  | n + 1, t => by
      refine Fin.lastCases ?_ (fun t ↦ ?_) t
      · intro c d h
        have hcd : c = d := by
          funext i
          exact h i (Fin.le_last i)
        subst d
        intro i j hi hj
        rfl
      · intro c d h
        let ec := secretaryRankCodeSnocEquiv n c
        let ed := secretaryRankCodeSnocEquiv n d
        rw [← (secretaryRankCodeSnocEquiv n).symm_apply_apply c,
          ← (secretaryRankCodeSnocEquiv n).symm_apply_apply d] at h ⊢
        rw [show (secretaryRankCodeSnocEquiv n).symm ec =
              secretaryRankCodeSnoc ec.1 ec.2 by rfl,
          show (secretaryRankCodeSnocEquiv n).symm ed =
              secretaryRankCodeSnoc ed.1 ed.2 by rfl] at h ⊢
        rw [secretaryPermOfRankCode_snoc, secretaryPermOfRankCode_snoc,
          sameRelativePrefix_snoc_castSucc]
        apply rankCodeAgreeThrough_sameRelativePrefix t ec.1 ed.1
        exact (rankCodeAgreeThrough_snoc_castSucc ec.1 ed.1 ec.2 ed.2 t).mp h

/-! ## Finite averaging on insertion codes -/

theorem sum_secretaryRankCode_snoc {n : ℕ} (f : SecretaryRankCode (n + 1) → ℝ) :
    ∑ c, f c = ∑ d : SecretaryRankCode n × Fin (n + 1),
      f (secretaryRankCodeSnoc d.1 d.2) := by
  exact (secretaryRankCodeSnocEquiv n).symm.sum_comp f |>.symm

theorem sum_secretaryRankCode_snoc' {n : ℕ} (f : SecretaryRankCode (n + 1) → ℝ) :
    ∑ c, f c = ∑ d : SecretaryRankCode n, ∑ p : Fin (n + 1),
      f (secretaryRankCodeSnoc d p) := by
  rw [sum_secretaryRankCode_snoc]
  rw [Fintype.sum_prod_type]

/-- A function of a rank path is adapted through `t` when it only depends on the code prefix. -/
def SecretaryCodeAdapted {m : ℕ} (t : Fin m) (f : SecretaryRankCode m → ℝ) : Prop :=
  ∀ c d, SecretaryRankCodeAgreeThrough t c d → f c = f d

theorem codeAdapted_snoc_const {n : ℕ} {t : Fin n}
    {f : SecretaryRankCode (n + 1) → ℝ} (hf : SecretaryCodeAdapted t.castSucc f)
    (c : SecretaryRankCode n) (p q : Fin (n + 1)) :
    f (secretaryRankCodeSnoc c p) = f (secretaryRankCodeSnoc c q) := by
  apply hf
  exact (rankCodeAgreeThrough_snoc_castSucc c c p q t).2
    (fun _ _ ↦ rfl)

theorem codeAdapted_init {n : ℕ} {t : Fin n}
    {f : SecretaryRankCode (n + 1) → ℝ} (hf : SecretaryCodeAdapted t.castSucc f)
    (p : Fin (n + 1)) :
    SecretaryCodeAdapted t (fun c ↦ f (secretaryRankCodeSnoc c p)) := by
  intro c d h
  exact hf _ _ ((rankCodeAgreeThrough_snoc_castSucc c d p p t).2 h)

/-- Dependence only on the strict prefix before `t`. -/
def SecretaryCodeBefore {m : ℕ} (t : Fin m) (f : SecretaryRankCode m → ℝ) : Prop :=
  ∀ c d, (∀ i : Fin m, i < t → c i = d i) → f c = f d

/-- The arrival at `t` is a record exactly when its insertion rank is the last rank.  The
value-level formulation avoids transports between definitionally equal `Fin` types. -/
abbrev SecretaryCodeRecord {m : ℕ} (c : SecretaryRankCode m) (t : Fin m) : Prop :=
  (c t).val = t.val

theorem codeBefore_snoc_const {n : ℕ} {t : Fin (n + 1)}
    {f : SecretaryRankCode (n + 1) → ℝ} (hf : SecretaryCodeBefore t f)
    (c : SecretaryRankCode n) (p q : Fin (n + 1)) :
    f (secretaryRankCodeSnoc c p) = f (secretaryRankCodeSnoc c q) := by
  apply hf
  intro i hi
  have hilast : i ≠ Fin.last n := by
    intro h
    subst i
    exact (not_lt_of_ge (Fin.le_last t)) hi
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hilast
  simp

theorem codeBefore_init {n : ℕ} {t : Fin n}
    {f : SecretaryRankCode (n + 1) → ℝ} (hf : SecretaryCodeBefore t.castSucc f)
    (p : Fin (n + 1)) :
    SecretaryCodeBefore t (fun c ↦ f (secretaryRankCodeSnoc c p)) := by
  intro c d h
  apply hf
  intro i hi
  have hilast : i ≠ Fin.last n := by
    intro hi'
    subst i
    exact (not_lt_of_ge t.castSucc_lt_last.le) hi
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hilast
  simpa using h i (by simpa using hi)

/-- Selecting one specified value of a future independent insertion rank divides its finite
sum by the cardinality of that rank coordinate. -/
theorem rankCode_record_sum_mul : ∀ {m : ℕ} (t : Fin m)
    (f : SecretaryRankCode m → ℝ), SecretaryCodeBefore t f →
      ((t.val + 1 : ℕ) : ℝ) *
          (∑ c, if SecretaryCodeRecord c t then f c else 0) = ∑ c, f c
  | 0, t => Fin.elim0 t
  | n + 1, t => by
      refine Fin.lastCases ?_ (fun t ↦ ?_) t
      · intro f hf
        change ((n + 1 : ℕ) : ℝ) *
          (∑ c, if SecretaryCodeRecord c (Fin.last n) then f c else 0) = ∑ c, f c
        rw [sum_secretaryRankCode_snoc' f]
        rw [sum_secretaryRankCode_snoc'
          (fun c ↦ if SecretaryCodeRecord c (Fin.last n) then f c else 0)]
        simp only [SecretaryCodeRecord, secretaryRankCodeSnoc_last, Fin.val_last]
        simp_rw [show ∀ p : Fin (n + 1), (p.val = n) = (p = Fin.last n) by
          intro p; apply propext; simp [Fin.ext_iff]]
        simp_rw [Finset.sum_ite_eq' Finset.univ (Fin.last n)]
        simp only [Finset.mem_univ, if_true]
        have hconst : ∀ (c : SecretaryRankCode n) (p : Fin (n + 1)),
            f (secretaryRankCodeSnoc c p) =
              f (secretaryRankCodeSnoc c (Fin.last n)) := by
          intro c p
          exact codeBefore_snoc_const hf c p (Fin.last n)
        simp_rw [hconst]
        simp [Finset.mul_sum]
      · intro f hf
        change ((t.val + 1 : ℕ) : ℝ) *
          (∑ c, if SecretaryCodeRecord c t.castSucc then f c else 0) = ∑ c, f c
        rw [sum_secretaryRankCode_snoc' f]
        rw [sum_secretaryRankCode_snoc'
          (fun c ↦ if SecretaryCodeRecord c t.castSucc then f c else 0)]
        simp only [SecretaryCodeRecord, secretaryRankCodeSnoc_castSucc, Fin.val_castSucc]
        let p0 : Fin (n + 1) := 0
        have hconst : ∀ (c : SecretaryRankCode n) (p : Fin (n + 1)),
            f (secretaryRankCodeSnoc c p) = f (secretaryRankCodeSnoc c p0) :=
          fun c p ↦ codeBefore_snoc_const hf c p p0
        simp_rw [hconst]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have ih := rankCode_record_sum_mul t (fun c ↦ f (secretaryRankCodeSnoc c p0))
          (codeBefore_init hf p0)
        have hscaled := congrArg (fun x : ℝ ↦ ((n + 1 : ℕ) : ℝ) * x) ih
        simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, mul_ite] using hscaled

/-- The item arriving at `t` is the largest of the entire horizon. -/
def SecretaryCodeGlobalMax {m : ℕ} (c : SecretaryRankCode m) (t : Fin m) : Prop :=
  secretaryPermOfRankCode c t =
    ⟨m - 1, Nat.sub_lt (Nat.zero_lt_of_lt t.isLt) (by omega)⟩

instance secretaryCodeGlobalMaxDecidable {m : ℕ} (c : SecretaryRankCode m) (t : Fin m) :
    Decidable (SecretaryCodeGlobalMax c t) := by
  unfold SecretaryCodeGlobalMax
  infer_instance

theorem codeGlobalMax_snoc_last {n : ℕ} (c : SecretaryRankCode n)
    (p : Fin (n + 1)) :
    SecretaryCodeGlobalMax (secretaryRankCodeSnoc c p) (Fin.last n) ↔
      SecretaryCodeRecord (secretaryRankCodeSnoc c p) (Fin.last n) := by
  simp [SecretaryCodeGlobalMax, SecretaryCodeRecord, Fin.ext_iff]

theorem codeGlobalMax_snoc_castSucc {n : ℕ} (c : SecretaryRankCode n)
    (p : Fin (n + 1)) (t : Fin n) :
    SecretaryCodeGlobalMax (secretaryRankCodeSnoc c p) t.castSucc ↔
      p ≠ Fin.last n ∧ SecretaryCodeGlobalMax c t := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ n =>
      simp only [SecretaryCodeGlobalMax, secretaryPermOfRankCode_snoc,
        secretaryPermSnoc_castSucc]
      constructor
      · intro h
        have hp : p ≠ Fin.last (n + 1) := by
          intro hp
          subst p
          simp only [Fin.succAbove_last_apply, Fin.ext_iff, Fin.val_castSucc] at h
          omega
        refine ⟨hp, ?_⟩
        exact (Fin.succAbove_eq_last_iff hp).mp h
      · rintro ⟨hp, ht⟩
        exact (Fin.succAbove_eq_last_iff hp).mpr ht

/-- Conditional on the rank history through `t`, the probability that its record is the
global maximum is `(t+1)/m`.  This is the exact finite counting identity used below. -/
theorem rankCode_globalMax_record_sum : ∀ {m : ℕ} (t : Fin m)
    (f : SecretaryRankCode m → ℝ), SecretaryCodeAdapted t f →
      (m : ℝ) * (∑ c, if SecretaryCodeGlobalMax c t then f c else 0) =
        ((t.val + 1 : ℕ) : ℝ) *
          (∑ c, if SecretaryCodeRecord c t then f c else 0)
  | 0, t => Fin.elim0 t
  | n + 1, t => by
      refine Fin.lastCases ?_ (fun t ↦ ?_) t
      · intro f hf
        rw [sum_secretaryRankCode_snoc'
          (fun c ↦ if SecretaryCodeGlobalMax c (Fin.last n) then f c else 0)]
        rw [sum_secretaryRankCode_snoc'
          (fun c ↦ if SecretaryCodeRecord c (Fin.last n) then f c else 0)]
        simp_rw [codeGlobalMax_snoc_last]
        simp
      · intro f hf
        rw [sum_secretaryRankCode_snoc'
          (fun c ↦ if SecretaryCodeGlobalMax c t.castSucc then f c else 0)]
        rw [sum_secretaryRankCode_snoc'
          (fun c ↦ if SecretaryCodeRecord c t.castSucc then f c else 0)]
        simp only [codeGlobalMax_snoc_castSucc, SecretaryCodeRecord,
          secretaryRankCodeSnoc_castSucc, Fin.val_castSucc]
        let p0 : Fin (n + 1) := 0
        have hconst : ∀ (c : SecretaryRankCode n) (p : Fin (n + 1)),
            f (secretaryRankCodeSnoc c p) = f (secretaryRankCodeSnoc c p0) :=
          fun c p ↦ codeAdapted_snoc_const hf c p p0
        simp_rw [hconst]
        have hnonlast (c : SecretaryRankCode n) :
            (∑ p : Fin (n + 1),
              if p ≠ Fin.last n ∧ SecretaryCodeGlobalMax c t then
                f (secretaryRankCodeSnoc c p0) else 0) =
              n * (if SecretaryCodeGlobalMax c t then
                f (secretaryRankCodeSnoc c p0) else 0) := by
          by_cases hc : SecretaryCodeGlobalMax c t
          · simp only [hc, and_true, if_true]
            rw [Finset.sum_ite]
            have hcard : (Finset.univ.filter (fun p : Fin (n + 1) ↦
                p ≠ Fin.last n)).card = n := by
              rw [Finset.filter_ne']
              simp
            simp [hcard]
          · simp [hc]
        simp_rw [hnonlast]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have ih := rankCode_globalMax_record_sum t
          (fun c ↦ f (secretaryRankCodeSnoc c p0)) (codeAdapted_init hf p0)
        have hscaled := congrArg (fun x : ℝ ↦ ((n + 1 : ℕ) : ℝ) * x) ih
        simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm, mul_ite] using hscaled

/-! ## Terminal stopping masses on rank codes -/

/-- Pull a classical rule back along the insertion-rank encoding. -/
def secretaryCodeStopMass {m : ℕ} (rule : ClassicalSecretaryRule m)
    (c : SecretaryRankCode m) (t : Fin m) : ℝ :=
  rule.stopProb (secretaryPermOfRankCode c) t

theorem secretaryCodeStopMass_nonneg {m : ℕ} (rule : ClassicalSecretaryRule m)
    (c : SecretaryRankCode m) (t : Fin m) :
    0 ≤ secretaryCodeStopMass rule c t :=
  rule.nonneg _ _

theorem secretaryCodeStopMass_total_le_one {m : ℕ} (rule : ClassicalSecretaryRule m)
    (c : SecretaryRankCode m) :
    ∑ t, secretaryCodeStopMass rule c t ≤ 1 :=
  rule.total_le_one _

theorem secretaryCodeStopMass_adapted {m : ℕ} (rule : ClassicalSecretaryRule m)
    (t : Fin m) : SecretaryCodeAdapted t (fun c ↦ secretaryCodeStopMass rule c t) := by
  intro c d h
  exact rule.causal _ _ t (rankCodeAgreeThrough_sameRelativePrefix t c d h)

theorem secretaryCodeGlobalMax_iff_winnerTime {m : ℕ} (hm : 1 ≤ m)
    (c : SecretaryRankCode m) (t : Fin m) :
    SecretaryCodeGlobalMax c t ↔
      t = (secretaryPermOfRankCode c).symm ⟨m - 1, by omega⟩ := by
  constructor
  · intro h
    apply (secretaryPermOfRankCode c).injective
    simpa [SecretaryCodeGlobalMax] using h
  · intro h
    subst t
    simp [SecretaryCodeGlobalMax]

theorem sum_globalMax_stopMass {m : ℕ} (hm : 1 ≤ m)
    (rule : ClassicalSecretaryRule m) (c : SecretaryRankCode m) :
    (∑ t, if SecretaryCodeGlobalMax c t then secretaryCodeStopMass rule c t else 0) =
      secretaryCodeStopMass rule c
        ((secretaryPermOfRankCode c).symm ⟨m - 1, by omega⟩) := by
  simp_rw [secretaryCodeGlobalMax_iff_winnerTime hm]
  rw [Finset.sum_ite_eq' Finset.univ
    ((secretaryPermOfRankCode c).symm ⟨m - 1, by omega⟩)]
  simp

/-- Rewrite classical success as the average of code stopping mass on global-maximum events. -/
theorem classicalSecretarySuccess_eq_codeGlobalMax {m : ℕ} (hm : 1 ≤ m)
    (rule : ClassicalSecretaryRule m) :
    classicalSecretarySuccess hm rule =
      ((Fintype.card (SecretaryRankCode m) : ℝ)⁻¹) *
        ∑ c : SecretaryRankCode m, ∑ t : Fin m,
          if SecretaryCodeGlobalMax c t then secretaryCodeStopMass rule c t else 0 := by
  unfold classicalSecretarySuccess
  rw [show Fintype.card (Equiv.Perm (Fin m)) =
      Fintype.card (SecretaryRankCode m) from
    Fintype.card_congr (secretaryPermRankCodeEquiv m)]
  rw [← (secretaryPermRankCodeEquiv m).symm.sum_comp
    (fun σ : Equiv.Perm (Fin m) ↦
      rule.stopProb σ (σ.symm ⟨m - 1, by omega⟩))]
  simp only [secretaryPermOfRankCode, secretaryCodeStopMass]
  apply congrArg (((Fintype.card (SecretaryRankCode m) : ℝ)⁻¹) * ·)
  apply Finset.sum_congr rfl
  intro c hc
  exact (sum_globalMax_stopMass hm rule c).symm

/-! ## The finite secretary linear program -/

/-- Total stopping mass on record histories at a fixed time. -/
def secretaryRecordStopSum {m : ℕ} (rule : ClassicalSecretaryRule m) (t : Fin m) : ℝ :=
  ∑ c : SecretaryRankCode m,
    if SecretaryCodeRecord c t then secretaryCodeStopMass rule c t else 0

/-- The conventional LP variable: conditional record-stopping mass multiplied by `t+1`. -/
def secretaryQ {m : ℕ} (rule : ClassicalSecretaryRule m) (t : Fin m) : ℝ :=
  (((t.val + 1 : ℕ) : ℝ) / Fintype.card (SecretaryRankCode m)) *
    secretaryRecordStopSum rule t

theorem secretaryQ_nonneg {m : ℕ} (rule : ClassicalSecretaryRule m) (t : Fin m) :
    0 ≤ secretaryQ rule t := by
  exact mul_nonneg (div_nonneg (by positivity) (by positivity))
    (Finset.sum_nonneg fun c _ ↦ by
      split
      · exact secretaryCodeStopMass_nonneg rule c t
      · exact le_rfl)

theorem classicalSecretarySuccess_eq_averageQ {m : ℕ} (hm : 1 ≤ m)
    (rule : ClassicalSecretaryRule m) :
    classicalSecretarySuccess hm rule = (m : ℝ)⁻¹ * ∑ t, secretaryQ rule t := by
  rw [classicalSecretarySuccess_eq_codeGlobalMax hm rule]
  rw [Finset.sum_comm]
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hcard : (Fintype.card (SecretaryRankCode m) : ℝ) ≠ 0 := by positivity
  have hglobal : ∀ t : Fin m,
      (∑ c : SecretaryRankCode m,
        if SecretaryCodeGlobalMax c t then secretaryCodeStopMass rule c t else 0) =
      (((t.val + 1 : ℕ) : ℝ) / m) * secretaryRecordStopSum rule t := by
    intro t
    have hcount := rankCode_globalMax_record_sum t
      (fun c ↦ secretaryCodeStopMass rule c t)
      (secretaryCodeStopMass_adapted rule t)
    unfold secretaryRecordStopSum
    field_simp
    nlinarith
  simp_rw [hglobal]
  simp only [secretaryQ]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  field_simp

/-- A record-weighted stopping term at time `i` depends only on the strict history before a
later time `t`. -/
theorem recordStop_before {m : ℕ} (rule : ClassicalSecretaryRule m) {i t : Fin m}
    (hit : i < t) : SecretaryCodeBefore t
      (fun c ↦ if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0) := by
  intro c d hcd
  have hcode : SecretaryRankCodeAgreeThrough i c d := by
    intro j hj
    exact hcd j (lt_of_le_of_lt hj hit)
  have hci : SecretaryCodeRecord c i ↔ SecretaryCodeRecord d i := by
    unfold SecretaryCodeRecord
    rw [hcode i le_rfl]
  change (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0) =
    if SecretaryCodeRecord d i then secretaryCodeStopMass rule d i else 0
  by_cases hc : SecretaryCodeRecord c i
  · rw [if_pos hc, if_pos (hci.mp hc)]
    exact secretaryCodeStopMass_adapted rule i c d hcode
  · rw [if_neg hc, if_neg (mt hci.mpr hc)]

/-- Exact cross-record double counting. -/
theorem crossRecordStopSum_mul {m : ℕ} (rule : ClassicalSecretaryRule m)
    {i t : Fin m} (hit : i < t) :
    (((t.val + 1 : ℕ) : ℝ) *
      ∑ c : SecretaryRankCode m,
        if SecretaryCodeRecord c t then
          (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
        else 0) = secretaryRecordStopSum rule i := by
  exact rankCode_record_sum_mul t
    (fun c ↦ if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
    (recordStop_before rule hit)

theorem recordCodeCount_mul {m : ℕ} (t : Fin m) :
    (((t.val + 1 : ℕ) : ℝ) *
      ∑ c : SecretaryRankCode m, if SecretaryCodeRecord c t then (1 : ℝ) else 0) =
      Fintype.card (SecretaryRankCode m) := by
  simpa using rankCode_record_sum_mul t (fun _ ↦ (1 : ℝ)) (by
    intro c d h
    rfl)

theorem codeStop_prefix_le_one {m : ℕ} (rule : ClassicalSecretaryRule m)
    (c : SecretaryRankCode m) (t : Fin m) :
    secretaryCodeStopMass rule c t +
        ∑ i ∈ Finset.Iio t,
          (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0) ≤ 1 := by
  have hrecords : (∑ i ∈ Finset.Iio t,
      (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)) ≤
      ∑ i ∈ Finset.Iio t, secretaryCodeStopMass rule c i := by
    apply Finset.sum_le_sum
    intro i hi
    split
    · exact le_rfl
    · exact secretaryCodeStopMass_nonneg rule c i
  have hshape : Finset.Iic t = insert t (Finset.Iio t) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Iio]
    omega
  have ht : t ∉ Finset.Iio t := by simp
  calc
    secretaryCodeStopMass rule c t +
        ∑ i ∈ Finset.Iio t,
          (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0) ≤
        secretaryCodeStopMass rule c t +
          ∑ i ∈ Finset.Iio t, secretaryCodeStopMass rule c i :=
      by simpa [add_comm] using add_le_add_left hrecords (secretaryCodeStopMass rule c t)
    _ = ∑ i ∈ Finset.Iic t, secretaryCodeStopMass rule c i := by
      rw [hshape, Finset.sum_insert ht]
    _ ≤ ∑ i, secretaryCodeStopMass rule c i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i hi hnot
      exact secretaryCodeStopMass_nonneg rule c i
    _ ≤ 1 := secretaryCodeStopMass_total_le_one rule c

/-- Summing the pathwise stopping budget over all histories having a record at `t`. -/
theorem aggregatedRecordBudget {m : ℕ} (rule : ClassicalSecretaryRule m) (t : Fin m) :
    secretaryRecordStopSum rule t +
      ∑ i ∈ Finset.Iio t,
        (∑ c : SecretaryRankCode m,
          if SecretaryCodeRecord c t then
            (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
          else 0) ≤
      ∑ c : SecretaryRankCode m, if SecretaryCodeRecord c t then (1 : ℝ) else 0 := by
  calc
    secretaryRecordStopSum rule t +
        ∑ i ∈ Finset.Iio t,
          (∑ c : SecretaryRankCode m,
            if SecretaryCodeRecord c t then
              (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
            else 0) =
        ∑ c : SecretaryRankCode m,
          if SecretaryCodeRecord c t then
            (secretaryCodeStopMass rule c t +
              ∑ i ∈ Finset.Iio t,
                if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
          else 0 := by
      simp only [secretaryRecordStopSum]
      rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hct : SecretaryCodeRecord c t
      · simp only [if_pos hct]
      · simp only [if_neg hct]
        simp
    _ ≤ ∑ c : SecretaryRankCode m,
          if SecretaryCodeRecord c t then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro c hc
      split
      · exact codeStop_prefix_le_one rule c t
      · exact le_rfl

/-- Feasibility constraints for the exact finite secretary LP. -/
theorem secretaryQ_constraint {m : ℕ} (rule : ClassicalSecretaryRule m) (t : Fin m) :
    secretaryQ rule t +
      ∑ i ∈ Finset.Iio t, secretaryQ rule i / ((i.val + 1 : ℕ) : ℝ) ≤ 1 := by
  have hbudget := aggregatedRecordBudget rule t
  have htpos : (0 : ℝ) < ((t.val + 1 : ℕ) : ℝ) := by positivity
  have hcard : (0 : ℝ) < Fintype.card (SecretaryRankCode m) := by positivity
  have hcross : ∀ i ∈ Finset.Iio t,
      (∑ c : SecretaryRankCode m,
        if SecretaryCodeRecord c t then
          (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
        else 0) = secretaryRecordStopSum rule i / ((t.val + 1 : ℕ) : ℝ) := by
    intro i hi
    have h := crossRecordStopSum_mul rule (Finset.mem_Iio.mp hi)
    exact (eq_div_iff htpos.ne').2 (by simpa [mul_comm] using h)
  rw [show (∑ i ∈ Finset.Iio t,
      (∑ c : SecretaryRankCode m,
        if SecretaryCodeRecord c t then
          (if SecretaryCodeRecord c i then secretaryCodeStopMass rule c i else 0)
        else 0)) =
      ∑ i ∈ Finset.Iio t,
        secretaryRecordStopSum rule i / ((t.val + 1 : ℕ) : ℝ) by
    apply Finset.sum_congr rfl
    intro i hi
    exact hcross i hi] at hbudget
  have hcount := recordCodeCount_mul t
  have hcount' : (∑ c : SecretaryRankCode m,
      if SecretaryCodeRecord c t then (1 : ℝ) else 0) =
      Fintype.card (SecretaryRankCode m) / ((t.val + 1 : ℕ) : ℝ) :=
    (eq_div_iff htpos.ne').2 (by simpa [mul_comm] using hcount)
  rw [hcount'] at hbudget
  simp only [secretaryQ]
  have hterm : ∀ i : Fin m,
      (((i.val + 1 : ℕ) : ℝ) / Fintype.card (SecretaryRankCode m) *
          secretaryRecordStopSum rule i) / ((i.val + 1 : ℕ) : ℝ) =
        secretaryRecordStopSum rule i / Fintype.card (SecretaryRankCode m) := by
    intro i
    have hipos : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by positivity
    field_simp
  simp_rw [hterm]
  calc
    ((t.val + 1 : ℕ) : ℝ) / Fintype.card (SecretaryRankCode m) *
          secretaryRecordStopSum rule t +
        ∑ i ∈ Finset.Iio t,
          secretaryRecordStopSum rule i / Fintype.card (SecretaryRankCode m) =
        (((t.val + 1 : ℕ) : ℝ) / Fintype.card (SecretaryRankCode m)) *
          (secretaryRecordStopSum rule t +
            ∑ i ∈ Finset.Iio t,
              secretaryRecordStopSum rule i / ((t.val + 1 : ℕ) : ℝ)) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ ≤ (((t.val + 1 : ℕ) : ℝ) / Fintype.card (SecretaryRankCode m)) *
        (Fintype.card (SecretaryRankCode m) / ((t.val + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget (div_nonneg htpos.le hcard.le)
    _ = 1 := by field_simp

/-! ## The attaining skip-then-record rule -/

/-- The current item is largest among the observations seen so far. -/
def SecretaryPermutationRecord {m : ℕ} (σ : Equiv.Perm (Fin m)) (t : Fin m) : Prop :=
  ∀ i : Fin m, i ≤ t → σ i ≤ σ t

instance secretaryPermutationRecordDecidable {m : ℕ} (σ : Equiv.Perm (Fin m))
    (t : Fin m) : Decidable (SecretaryPermutationRecord σ t) := Classical.dec _

theorem permutationRecord_snoc_last {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) :
    SecretaryPermutationRecord (secretaryPermSnoc e p) (Fin.last n) ↔
      p = Fin.last n := by
  constructor
  · intro h
    by_contra hp
    let q : Fin n := p.castPred hp
    let i : Fin n := e.symm q
    have hle := h i.castSucc (Fin.le_last _)
    simp only [secretaryPermSnoc_castSucc, secretaryPermSnoc_last] at hle
    have hlt : p < p.succAbove (e i) := by
      simp only [i, Equiv.apply_symm_apply]
      rw [Fin.lt_succAbove_iff_le_castSucc]
      simp [q]
    exact (not_lt_of_ge hle) hlt
  · rintro rfl
    intro i hi
    rw [secretaryPermSnoc_last]
    exact Fin.le_last _

theorem permutationRecord_snoc_castSucc {n : ℕ} (e : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) (t : Fin n) :
    SecretaryPermutationRecord (secretaryPermSnoc e p) t.castSucc ↔
      SecretaryPermutationRecord e t := by
  constructor
  · intro h i hi
    have h' := h i.castSucc (by simpa)
    simpa only [secretaryPermSnoc_castSucc, Fin.succAbove_le_succAbove_iff] using h'
  · intro h i hi
    have hilast : i ≠ Fin.last n := by
      intro hilast
      subst i
      exact (not_le_of_gt t.castSucc_lt_last) hi
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hilast
    simpa only [secretaryPermSnoc_castSucc, Fin.succAbove_le_succAbove_iff] using
      h i (by simpa using hi)

/-- The insertion rank is maximal exactly when the current permutation value is a record. -/
theorem codeRecord_iff_permutationRecord : ∀ {m : ℕ} (c : SecretaryRankCode m) (t : Fin m),
    SecretaryCodeRecord c t ↔ SecretaryPermutationRecord (secretaryPermOfRankCode c) t
  | 0, c, t => Fin.elim0 t
  | n + 1, c, t => by
      let cp := secretaryRankCodeSnocEquiv n c
      have hc : c = secretaryRankCodeSnoc cp.1 cp.2 := by
        change c = (secretaryRankCodeSnocEquiv n).symm
          (secretaryRankCodeSnocEquiv n c)
        exact ((secretaryRankCodeSnocEquiv n).symm_apply_apply c).symm
      rw [hc]
      change SecretaryCodeRecord (secretaryRankCodeSnoc cp.1 cp.2) t ↔ _
      rw [secretaryPermOfRankCode_snoc]
      refine Fin.lastCases ?_ (fun t ↦ ?_) t
      · simp only [SecretaryCodeRecord, secretaryRankCodeSnoc_last, Fin.val_last]
        rw [permutationRecord_snoc_last]
        simp [Fin.ext_iff]
      · simp only [SecretaryCodeRecord, secretaryRankCodeSnoc_castSucc, Fin.val_castSucc]
        rw [permutationRecord_snoc_castSucc]
        exact codeRecord_iff_permutationRecord cp.1 t

theorem permutationRecord_congr {m : ℕ} {σ τ : Equiv.Perm (Fin m)} {t : Fin m}
    (h : SameRelativePrefix t σ τ) :
    SecretaryPermutationRecord σ t ↔ SecretaryPermutationRecord τ t := by
  constructor
  · intro hs i hi
    apply not_lt.mp
    intro hlt
    have hrel := h t i le_rfl hi
    exact (not_lt_of_ge (hs i hi)) (hrel.mpr hlt)
  · intro ht i hi
    apply not_lt.mp
    intro hlt
    have hrel := h t i le_rfl hi
    exact (not_lt_of_ge (ht i hi)) (hrel.mp hlt)

/-- Select the first record whose zero-based time is at least `skip`. -/
def SecretaryThresholdSelect {m : ℕ} (skip : ℕ) (σ : Equiv.Perm (Fin m))
    (t : Fin m) : Prop :=
  skip ≤ t.val ∧ SecretaryPermutationRecord σ t ∧
    ∀ i : Fin m, skip ≤ i.val → i < t → ¬SecretaryPermutationRecord σ i

instance secretaryThresholdSelectDecidable {m : ℕ} (skip : ℕ)
    (σ : Equiv.Perm (Fin m)) (t : Fin m) :
    Decidable (SecretaryThresholdSelect skip σ t) := Classical.dec _

theorem thresholdSelect_congr {m : ℕ} (skip : ℕ) {σ τ : Equiv.Perm (Fin m)}
    {t : Fin m} (h : SameRelativePrefix t σ τ) :
    SecretaryThresholdSelect skip σ t ↔ SecretaryThresholdSelect skip τ t := by
  have hrec := permutationRecord_congr h
  constructor
  · rintro ⟨hskip, hrecord, hfirst⟩
    refine ⟨hskip, hrec.mp hrecord, ?_⟩
    intro i hsi hit hτi
    apply hfirst i hsi hit
    apply (permutationRecord_congr (t := i) (σ := σ) (τ := τ) ?_).mpr hτi
    intro a b ha hb
    exact h a b (le_trans ha hit.le) (le_trans hb hit.le)
  · rintro ⟨hskip, hrecord, hfirst⟩
    refine ⟨hskip, hrec.mpr hrecord, ?_⟩
    intro i hsi hit hσi
    apply hfirst i hsi hit
    apply (permutationRecord_congr (t := i) (σ := σ) (τ := τ) ?_).mp hσi
    intro a b ha hb
    exact h a b (le_trans ha hit.le) (le_trans hb hit.le)

theorem thresholdSelect_unique {m : ℕ} {skip : ℕ} {σ : Equiv.Perm (Fin m)}
    {t u : Fin m} (ht : SecretaryThresholdSelect skip σ t)
    (hu : SecretaryThresholdSelect skip σ u) : t = u := by
  rcases lt_trichotomy t u with htu | htu | htu
  · exact False.elim (hu.2.2 t ht.1 htu ht.2.1)
  · exact htu
  · exact False.elim (ht.2.2 u hu.1 htu hu.2.1)

/-- The deterministic rule rejecting `skip` observations and then taking the first record. -/
def secretaryThresholdRule (m skip : ℕ) : ClassicalSecretaryRule m where
  stopProb := fun σ t ↦ if SecretaryThresholdSelect skip σ t then 1 else 0
  nonneg := by
    intro σ t
    split <;> norm_num
  total_le_one := by
    intro σ
    have hcard : (Finset.univ.filter
        (fun t : Fin m ↦ SecretaryThresholdSelect skip σ t)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro t ht u hu
      exact thresholdSelect_unique (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hu).2
    rw [show (∑ t : Fin m, if SecretaryThresholdSelect skip σ t then (1 : ℝ) else 0) =
        ((Finset.univ.filter
          (fun t : Fin m ↦ SecretaryThresholdSelect skip σ t)).card : ℝ) by
      simpa using Finset.sum_boole
        (fun t : Fin m ↦ SecretaryThresholdSelect skip σ t) Finset.univ]
    exact_mod_cast hcard
  causal := by
    intro σ τ t h
    rw [if_congr (thresholdSelect_congr skip h) rfl rfl]

/-- No record occurs at a zero-based time in the half-open interval `[skip, before)`. -/
def SecretaryCodeNoRecord {m : ℕ} (skip before : ℕ) (c : SecretaryRankCode m) : Prop :=
  ∀ i : Fin m, skip ≤ i.val → i.val < before → ¬SecretaryCodeRecord c i

instance secretaryCodeNoRecordDecidable {m : ℕ} (skip before : ℕ)
    (c : SecretaryRankCode m) : Decidable (SecretaryCodeNoRecord skip before c) :=
  Classical.dec _

def secretaryNoRecordCount (m skip before : ℕ) : ℝ :=
  ∑ c : SecretaryRankCode m, if SecretaryCodeNoRecord skip before c then (1 : ℝ) else 0

theorem secretaryCodeNoRecord_self {m skip : ℕ} (c : SecretaryRankCode m) :
    SecretaryCodeNoRecord skip skip c := by
  intro i hlo hhi
  omega

theorem secretaryNoRecordCount_self (m skip : ℕ) :
    secretaryNoRecordCount m skip skip = Fintype.card (SecretaryRankCode m) := by
  simp [secretaryNoRecordCount, secretaryCodeNoRecord_self]

theorem secretaryCodeNoRecord_succ_iff {m skip b : ℕ} (hsb : skip ≤ b)
    (hb : b < m) (c : SecretaryRankCode m) :
    SecretaryCodeNoRecord skip (b + 1) c ↔
      SecretaryCodeNoRecord skip b c ∧
        ¬SecretaryCodeRecord c ⟨b, hb⟩ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hsi hib
      exact h i hsi (by omega)
    · exact h ⟨b, hb⟩ hsb (by simp)
  · rintro ⟨hbefore, hbrec⟩ i hsi hi
    by_cases hib : i.val < b
    · exact hbefore i hsi hib
    · have hit : i = (⟨b, hb⟩ : Fin m) := by
        apply Fin.ext
        change i.val = b
        omega
      simpa [hit] using hbrec

theorem noRecordIndicator_before {m skip b : ℕ} (hb : b < m) :
    SecretaryCodeBefore (⟨b, hb⟩ : Fin m)
      (fun c ↦ if SecretaryCodeNoRecord skip b c then (1 : ℝ) else 0) := by
  intro c d hcd
  have hiff : SecretaryCodeNoRecord skip b c ↔ SecretaryCodeNoRecord skip b d := by
    constructor
    · intro hc i hsi hib hdi
      apply hc i hsi hib
      have heq := hcd i (show i < (⟨b, hb⟩ : Fin m) by exact hib)
      unfold SecretaryCodeRecord at hdi ⊢
      simpa [heq] using hdi
    · intro hd i hsi hib hci
      apply hd i hsi hib
      have heq := hcd i (show i < (⟨b, hb⟩ : Fin m) by exact hib)
      unfold SecretaryCodeRecord at hci ⊢
      simpa [heq] using hci
  exact if_congr hiff rfl rfl

/-- One more non-record coordinate multiplies the count by `b/(b+1)`. -/
theorem secretaryNoRecordCount_step {m skip b : ℕ} (hsb : skip ≤ b) (hb : b < m) :
    (((b + 1 : ℕ) : ℝ) * secretaryNoRecordCount m skip (b + 1)) =
      (b : ℝ) * secretaryNoRecordCount m skip b := by
  let t : Fin m := ⟨b, hb⟩
  let f : SecretaryRankCode m → ℝ :=
    fun c ↦ if SecretaryCodeNoRecord skip b c then (1 : ℝ) else 0
  have hrecord := rankCode_record_sum_mul t f (noRecordIndicator_before hb)
  have hpartition : secretaryNoRecordCount m skip (b + 1) +
      (∑ c : SecretaryRankCode m,
        if SecretaryCodeRecord c t then f c else 0) =
      secretaryNoRecordCount m skip b := by
    unfold secretaryNoRecordCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hn : SecretaryCodeNoRecord skip b c
    · by_cases hr : SecretaryCodeRecord c t <;>
        simp [secretaryCodeNoRecord_succ_iff hsb hb, f, t, hn, hr]
    · simp [secretaryCodeNoRecord_succ_iff hsb hb, f, t, hn]
  change (((b + 1 : ℕ) : ℝ) *
      (∑ c, if SecretaryCodeRecord c t then f c else 0)) =
    secretaryNoRecordCount m skip b at hrecord
  push_cast at hrecord ⊢
  nlinarith

/-- Closed form for the no-record count. -/
theorem secretaryNoRecordCount_mul {m skip b : ℕ} (hsb : skip ≤ b) (hbm : b ≤ m) :
    (b : ℝ) * secretaryNoRecordCount m skip b =
      (skip : ℝ) * Fintype.card (SecretaryRankCode m) := by
  induction b, hsb using Nat.le_induction with
  | base => simp [secretaryNoRecordCount_self]
  | succ b hsb ih =>
      have hbm' : b < m := by omega
      rw [secretaryNoRecordCount_step hsb hbm']
      exact ih (by omega)

theorem thresholdSelect_decode_iff {m skip : ℕ} (c : SecretaryRankCode m) (t : Fin m) :
    SecretaryThresholdSelect skip (secretaryPermOfRankCode c) t ↔
      skip ≤ t.val ∧ SecretaryCodeRecord c t ∧
        SecretaryCodeNoRecord skip t.val c := by
  constructor
  · rintro ⟨hskip, hrec, hfirst⟩
    refine ⟨hskip, (codeRecord_iff_permutationRecord c t).2 hrec, ?_⟩
    intro i hsi hit
    exact fun hci ↦ hfirst i hsi (by exact hit)
      ((codeRecord_iff_permutationRecord c i).1 hci)
  · rintro ⟨hskip, hrec, hfirst⟩
    refine ⟨hskip, (codeRecord_iff_permutationRecord c t).1 hrec, ?_⟩
    intro i hsi hit hirec
    exact hfirst i hsi hit ((codeRecord_iff_permutationRecord c i).2 hirec)

@[simp]
theorem thresholdCodeStopMass {m skip : ℕ} (c : SecretaryRankCode m) (t : Fin m) :
    secretaryCodeStopMass (secretaryThresholdRule m skip) c t =
      if skip ≤ t.val ∧ SecretaryCodeRecord c t ∧
          SecretaryCodeNoRecord skip t.val c then 1 else 0 := by
  unfold secretaryCodeStopMass secretaryThresholdRule
  change (if SecretaryThresholdSelect skip (secretaryPermOfRankCode c) t then 1 else 0) = _
  rw [if_congr (thresholdSelect_decode_iff c t) rfl rfl]

theorem thresholdRecordStopSum_mul {m skip : ℕ} (t : Fin m) (hst : skip ≤ t.val) :
    (((t.val + 1 : ℕ) : ℝ) *
      secretaryRecordStopSum (secretaryThresholdRule m skip) t) =
      secretaryNoRecordCount m skip t.val := by
  let f : SecretaryRankCode m → ℝ :=
    fun c ↦ if SecretaryCodeNoRecord skip t.val c then (1 : ℝ) else 0
  have hrecord := rankCode_record_sum_mul t f (noRecordIndicator_before t.isLt)
  unfold secretaryRecordStopSum
  convert hrecord using 1
  · apply congrArg (((t.val + 1 : ℕ) : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro c hc
    simp only [thresholdCodeStopMass]
    by_cases hr : SecretaryCodeRecord c t
    · by_cases hn : SecretaryCodeNoRecord skip t.val c <;> simp [f, hst, hr, hn]
    · simp [f, hst, hr]
  · unfold secretaryNoRecordCount
    rfl

theorem thresholdQ_of_pos {m skip : ℕ} (hskip : 1 ≤ skip) (t : Fin m) :
    secretaryQ (secretaryThresholdRule m skip) t =
      if skip ≤ t.val then (skip : ℝ) / t.val else 0 := by
  by_cases hst : skip ≤ t.val
  · rw [if_pos hst]
    have htposN : 0 < t.val := lt_of_lt_of_le Nat.zero_lt_one (hskip.trans hst)
    have htpos : (0 : ℝ) < t.val := by exact_mod_cast htposN
    have hrec := thresholdRecordStopSum_mul t hst
    have hno := secretaryNoRecordCount_mul hst (Nat.le_of_lt t.isLt)
    unfold secretaryQ
    have hcard : (0 : ℝ) < Fintype.card (SecretaryRankCode m) := by positivity
    field_simp
    nlinarith
  · rw [if_neg hst]
    unfold secretaryQ secretaryRecordStopSum
    have hzero : ∀ c : SecretaryRankCode m,
        (if SecretaryCodeRecord c t then
          secretaryCodeStopMass (secretaryThresholdRule m skip) c t else 0) = 0 := by
      intro c
      simp [thresholdCodeStopMass, hst]
    simp_rw [hzero]
    simp

/-- Shift a sum over zero-based finite times to the manuscript's one-based interval. -/
theorem sum_fin_ge_eq_Icc_shift (m skip : ℕ) (F : ℕ → ℝ) :
    (∑ t : Fin m, if skip ≤ t.val then F t.val else 0) =
      ∑ u ∈ Finset.Icc (skip + 1) m, F (u - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      by_cases hsm : skip ≤ m
      · rw [Finset.sum_Icc_succ_top (by omega)]
        simp [hsm]
      · have hempty : Finset.Icc (skip + 1) (m + 1) = ∅ := by
          apply Finset.Icc_eq_empty_of_lt
          omega
        have hempty' : Finset.Icc (skip + 1) m = ∅ := by
          apply Finset.Icc_eq_empty_of_lt
          omega
        rw [hempty, hempty']
        simp [hsm]

/-- Exact success of the skip-then-record rule for a positive number of rejected items. -/
theorem secretaryThresholdRule_success_of_pos {m skip : ℕ} (hm : 1 ≤ m)
    (hskip : 1 ≤ skip) (hsm : skip < m) :
    classicalSecretarySuccess hm (secretaryThresholdRule m skip) =
      secretaryCandidate m (skip + 1) := by
  rw [classicalSecretarySuccess_eq_averageQ hm]
  simp_rw [thresholdQ_of_pos hskip]
  rw [sum_fin_ge_eq_Icc_shift m skip (fun k ↦ (skip : ℝ) / k)]
  have hne : skip + 1 ≠ 1 := by omega
  rw [secretaryCandidate]
  simp only [hne, if_false, Nat.add_sub_cancel]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

theorem thresholdQ_zero_time {m : ℕ} (hm : 1 ≤ m) :
    secretaryQ (secretaryThresholdRule m 0) (⟨0, by omega⟩ : Fin m) = 1 := by
  let t : Fin m := ⟨0, by omega⟩
  have hrec := thresholdRecordStopSum_mul (skip := 0) t (by omega)
  have hno := secretaryNoRecordCount_self m 0
  change secretaryQ (secretaryThresholdRule m 0) t = 1
  unfold secretaryQ
  simp only [t, Nat.zero_add, Nat.cast_one]
  simp only [t, Nat.zero_add, Nat.cast_one, one_mul] at hrec
  rw [hno] at hrec
  have hc : (Fintype.card (SecretaryRankCode m) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem secretaryThresholdRule_success_one :
    classicalSecretarySuccess (m := 1) (by omega) (secretaryThresholdRule 1 0) = 1 := by
  rw [classicalSecretarySuccess_eq_averageQ (by omega)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.isValue, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  norm_num
  exact thresholdQ_zero_time (m := 1) (by omega)

theorem secretaryCandidate_one_le_two {m : ℕ} (hm : 2 ≤ m) :
    secretaryCandidate m 1 ≤ secretaryCandidate m 2 := by
  rw [secretaryCandidate_one]
  have h2mem : 2 ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨le_rfl, hm⟩
  have hsum : (1 : ℝ) ≤
      ∑ t ∈ Finset.Icc 2 m, (((t - 1 : ℕ) : ℝ)⁻¹) := by
    have h := Finset.single_le_sum
      (s := Finset.Icc 2 m) (f := fun t : ℕ ↦ (((t - 1 : ℕ) : ℝ)⁻¹))
      (fun t ht ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) h2mem
    norm_num at h ⊢
    exact h
  rw [secretaryCandidate, if_neg (by omega : (2 : ℕ) ≠ 1)]
  norm_num
  simpa using mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Nat.cast_nonneg m))

/-- Exact classical finite-horizon upper bound used by `lem:ramsey-erasure` and
`thm:full-secretary-success`. -/
theorem classicalSecretaryUpperBound : External.ClassicalSecretaryUpperBound := by
  intro m hm rule
  rw [classicalSecretarySuccess_eq_averageQ hm rule]
  exact classicalSecretaryLP_upper hm (secretaryQ rule)
    (secretaryQ_nonneg rule) (secretaryQ_constraint rule)

/-- An explicit skip-then-record rule attains the finite value required by
`thm:full-secretary-success`, including `m = 1`. -/
theorem classicalSecretaryAttainment : External.ClassicalSecretaryAttainment := by
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    refine ⟨secretaryThresholdRule 1 0, ?_⟩
    rw [secretaryS_one, secretaryThresholdRule_success_one]
  · have hm2 : 2 ≤ m := by omega
    let s : Finset ℕ := Finset.Icc 1 m
    have hs : s.Nonempty :=
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hm⟩⟩
    obtain ⟨r, hr, hmax⟩ := Finset.exists_mem_eq_sup' hs (secretaryCandidate m)
    have hrange : 1 ≤ r ∧ r ≤ m := Finset.mem_Icc.1 hr
    by_cases hr1 : r = 1
    · refine ⟨secretaryThresholdRule m 1, ?_⟩
      rw [secretaryS_eq_max hm]
      change s.sup' hs (secretaryCandidate m) ≤ _
      rw [secretaryThresholdRule_success_of_pos hm (by omega) (by omega)]
      rw [hmax]
      simpa [hr1] using secretaryCandidate_one_le_two hm2
    · refine ⟨secretaryThresholdRule m (r - 1), ?_⟩
      rw [secretaryS_eq_max hm]
      change s.sup' hs (secretaryCandidate m) ≤ _
      rw [secretaryThresholdRule_success_of_pos hm (by omega) (by omega)]
      rw [show r - 1 + 1 = r by omega]
      exact hmax.le

/-- The closed exact finite classical-secretary interface for `thm:full-secretary-success`. -/
theorem classicalSecretaryFinite : External.ClassicalSecretaryFinite :=
  ⟨classicalSecretaryUpperBound, classicalSecretaryAttainment⟩

end

end MomentAmbiguity
